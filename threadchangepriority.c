/**
 * @file
 *
 * @brief Changes the Priority of a Thread
 *
 * @ingroup RTEMSScoreThread
 */

/*
 *  COPYRIGHT (c) 1989-2014.
 *  On-Line Applications Research Corporation (OAR).
 *
 *  Copyright (c) 2013, 2016 embedded brains GmbH
 *
 *  The license and distribution terms for this file may be
 *  found in the file LICENSE in this distribution or at
 *  http://www.rtems.org/license/LICENSE.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include <rtems/score/threadimpl.h>
#include <rtems/score/assert.h>
#include <rtems/score/schedulerimpl.h>

/*@ ghost
  Scheduler_Node *g_scheduler_node_of_wait_priority_node;
  Priority_Node *g_min_priority_node;
  bool g_new_minimum;
*/
/*@
 requires \valid(priority_aggregation) && \valid(g_scheduler_node_of_wait_priority_node);
 
 assigns g_scheduler_node_of_wait_priority_node->Priority.value;
 
 behavior prepend:
  assumes prepend_it;
  ensures g_scheduler_node_of_wait_priority_node->Priority.value == (\old(priority_aggregation->Node.priority) | 0);
 
 behavior no_prepend:
  assumes !prepend_it;
  ensures g_scheduler_node_of_wait_priority_node->Priority.value == (\old(priority_aggregation->Node.priority) | 1);
 
 disjoint behaviors;
 complete behaviors;
 */
static void _Thread_Set_scheduler_node_priority(
    Priority_Aggregation *priority_aggregation,
    bool prepend_it)
{
  /*   
  _Scheduler_Node_set_priority(
      SCHEDULER_NODE_OF_WAIT_PRIORITY_NODE( priority_aggregation ),
      _Priority_Get_priority( priority_aggregation ),
      prepend_it
    ); 
  */

  _Scheduler_Node_set_priority(
      _Helper_SCHEDULER_NODE_OF_WAIT_PRIORITY_NODE(priority_aggregation),
      _Priority_Get_priority(priority_aggregation),
      prepend_it);
}

#if defined(RTEMS_SMP)
static void _Thread_Priority_action_add(
    Priority_Aggregation *priority_aggregation,
    Priority_Actions *priority_actions,
    void *arg)
{
  Scheduler_Node *scheduler_node;
  Thread_Control *the_thread;

  scheduler_node = SCHEDULER_NODE_OF_WAIT_PRIORITY(priority_aggregation);
  the_thread = arg;

  _Thread_Scheduler_add_wait_node(the_thread, scheduler_node);
  _Thread_Set_scheduler_node_priority(priority_aggregation, false);
  _Priority_Set_action_type(priority_aggregation, PRIORITY_ACTION_ADD);
  _Priority_Actions_add(priority_actions, priority_aggregation);
}

static void _Thread_Priority_action_remove(
    Priority_Aggregation *priority_aggregation,
    Priority_Actions *priority_actions,
    void *arg)
{
  Scheduler_Node *scheduler_node;
  Thread_Control *the_thread;

  scheduler_node = SCHEDULER_NODE_OF_WAIT_PRIORITY(priority_aggregation);
  the_thread = arg;

  _Thread_Scheduler_remove_wait_node(the_thread, scheduler_node);
  _Thread_Set_scheduler_node_priority(priority_aggregation, true);
  _Priority_Set_action_type(priority_aggregation, PRIORITY_ACTION_REMOVE);
  _Priority_Actions_add(priority_actions, priority_aggregation);
}
#endif

/*@
  requires
    \valid(priority_aggregation) &&
    \valid(priority_actions) &&
    \valid(g_scheduler_node_of_wait_priority_node);
  
  assigns g_scheduler_node_of_wait_priority_node->Priority.value;
  assigns priority_actions->actions;
  
  behavior prepend:
   assumes prepend_it;
   ensures g_scheduler_node_of_wait_priority_node->Priority.value
    == (\old(priority_aggregation->Node.priority) | 0);
   ensures priority_actions->actions == priority_aggregation;
  
  behavior no_prepend:
   assumes !prepend_it;
   ensures g_scheduler_node_of_wait_priority_node->Priority.value
    == (\old(priority_aggregation->Node.priority) | 1);
   ensures priority_actions->actions == priority_aggregation;
  
  disjoint behaviors;
  complete behaviors;
*/
static void _Thread_Priority_action_change(
    Priority_Aggregation *priority_aggregation,
    bool prepend_it,
    Priority_Actions *priority_actions,
    void *arg)
{
  _Thread_Set_scheduler_node_priority(priority_aggregation, prepend_it);
#if defined(RTEMS_SMP) || defined(RTEMS_DEBUG)
  _Priority_Set_action_type(priority_aggregation, PRIORITY_ACTION_CHANGE);
#endif

  _Priority_Actions_add(priority_actions, priority_aggregation);

}

/*@
  logic Priority_Action_type Get_Priority_Action_type(Thread_queue_Context *t) =
    (t->Priority.Actions.actions)->Action.type;
  logic Priority_Node *Get_Priority_Action_node(Thread_queue_Context *t) =
    (t->Priority.Actions.actions)->Action.node;
  logic Priority_Aggregation *Get_Priority_Aggregation(Thread_queue_Context *t) =
    (t->Priority.Actions.actions);
*/

/*@
  requires \valid(the_thread);
  requires \valid(queue);
  requires \valid(operations);
  requires \valid(queue_context);
  requires \valid(g_scheduler_node_of_wait_priority_node) && \valid(g_min_priority_node);
  requires
    \valid(Get_Priority_Aggregation(queue_context)) &&
    \valid(Get_Priority_Action_node(queue_context));
  requires \valid(queue_context->Priority.update[0]);
  requires queue_context->Priority.update_count == 0;
  requires operations->priority_actions == _Thread_queue_Do_nothing_priority_actions;
  requires the_thread->Wait.operations == operations;
  requires (the_thread->Scheduler.nodes)->Wait.Priority.Action.node
   == Get_Priority_Action_node(queue_context);

  requires 
    \separated(
      &Get_Priority_Aggregation(queue_context)->Node.priority,
      &g_scheduler_node_of_wait_priority_node->Priority.value,
      &g_min_priority_node->priority,
      &Get_Priority_Action_node(queue_context)->priority,
      &queue_context->Priority.update_count
    );

  requires Get_Priority_Aggregation(queue_context) == &the_thread->Scheduler.nodes->Wait.Priority;
  requires Get_Priority_Action_type(queue_context) \in {PRIORITY_ACTION_ADD, PRIORITY_ACTION_REMOVE, PRIORITY_ACTION_CHANGE};

  ensures queue_context->Priority.Actions.actions == NULL;
  ensures \valid(&queue_context->Priority.Actions);

  behavior priority_add_new_minimum:
    assumes Get_Priority_Action_type(queue_context) == PRIORITY_ACTION_ADD;
    assumes g_new_minimum;
    assigns g_scheduler_node_of_wait_priority_node->Priority.value, Get_Priority_Aggregation(queue_context)->Node.priority,
      queue_context->Priority.update[0], queue_context->Priority.update_count;
    assigns queue_context->Priority.Actions.actions;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value ==
        (\old(Get_Priority_Action_node(queue_context)->priority) | 1);
    ensures \old(Get_Priority_Aggregation(queue_context))->Node.priority == \old(Get_Priority_Action_node(queue_context)->priority);
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_add_no_new_minimum:
    assumes Get_Priority_Action_type(queue_context) == PRIORITY_ACTION_ADD;
    assumes !g_new_minimum;
    assigns queue_context->Priority.Actions.actions;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value ==
        \old(g_scheduler_node_of_wait_priority_node->Priority.value );

  behavior priority_remove_new_minimum:
    assumes Get_Priority_Action_type(queue_context) == PRIORITY_ACTION_REMOVE;
    assumes Get_Priority_Action_node(queue_context)->priority < g_min_priority_node->priority;
    assigns g_scheduler_node_of_wait_priority_node->Priority.value, Get_Priority_Aggregation(queue_context)->Node.priority,
      queue_context->Priority.update[0], queue_context->Priority.update_count;
    assigns queue_context->Priority.Actions.actions;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value ==
        (g_min_priority_node->priority | 0);
    ensures \old(Get_Priority_Aggregation(queue_context))->Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_remove_no_new_minimum:
    assumes Get_Priority_Action_type(queue_context) == PRIORITY_ACTION_REMOVE;
    assumes !(Get_Priority_Action_node(queue_context)->priority < g_min_priority_node->priority);
    assigns queue_context->Priority.Actions.actions;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value ==
        \old(g_scheduler_node_of_wait_priority_node->Priority.value );

  behavior priority_change_new_minimum:
    assumes Get_Priority_Action_type(queue_context) == PRIORITY_ACTION_CHANGE;
    assumes Get_Priority_Aggregation(queue_context)->Node.priority != g_min_priority_node->priority;
    assumes !prepend_it;
    assigns g_scheduler_node_of_wait_priority_node->Priority.value, Get_Priority_Aggregation(queue_context)->Node.priority,
      queue_context->Priority.update[0], queue_context->Priority.update_count;
    assigns queue_context->Priority.Actions.actions;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value ==
        (g_min_priority_node->priority | 1);
    ensures \old(Get_Priority_Aggregation(queue_context))->Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_change_new_minimum_prepend:
    assumes Get_Priority_Action_type(queue_context) == PRIORITY_ACTION_CHANGE;
    assumes Get_Priority_Aggregation(queue_context)->Node.priority != g_min_priority_node->priority;
    assumes prepend_it;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      Get_Priority_Aggregation(queue_context)->Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count;
    assigns queue_context->Priority.Actions.actions;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value ==
        (g_min_priority_node->priority | 0);
    ensures \old(Get_Priority_Aggregation(queue_context))->Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_change_no_new_minimum:
    assumes Get_Priority_Action_type(queue_context) == PRIORITY_ACTION_CHANGE;
    assumes Get_Priority_Aggregation(queue_context)->Node.priority == g_min_priority_node->priority;
    assigns queue_context->Priority.Actions.actions;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value ==
      \old(g_scheduler_node_of_wait_priority_node->Priority.value );

 complete behaviors;
 disjoint behaviors;
 */
static void _Thread_Priority_do_perform_actions(
    Thread_Control *the_thread,
    Thread_queue_Queue *queue,
    const Thread_queue_Operations *operations,
    bool prepend_it,
    Thread_queue_Context *queue_context)
{
  Priority_Aggregation *priority_aggregation;

  _Assert(!_Priority_Actions_is_empty(&queue_context->Priority.Actions));
  priority_aggregation = _Priority_Actions_move(&queue_context->Priority.Actions);
  // assert priority_aggregation == \at(queue_context->Priority.Actions.actions, Pre);
  // assert priority_aggregation != NULL;
  // assert queue_context->Priority.Actions.actions == NULL;
  do
  {
  Priority_Aggregation *next_aggregation;
  Priority_Node *priority_action_node;
  Priority_Action_type priority_action_type;
  
  next_aggregation = _Priority_Get_next_action(priority_aggregation);

  priority_action_node = priority_aggregation->Action.node;
  priority_action_type = priority_aggregation->Action.type;

  switch (priority_action_type)
  {
  case PRIORITY_ACTION_ADD:
#if defined(RTEMS_SMP)
    _Priority_Insert(
        priority_aggregation,
        priority_action_node,
        &queue_context->Priority.Actions,
        _Thread_Priority_action_add,
        _Thread_Priority_action_change,
        the_thread);
#else
    _Priority_Non_empty_insert(
        priority_aggregation,
        priority_action_node,
        &queue_context->Priority.Actions,
        _Thread_Priority_action_change,
        NULL);
    // assert priority_aggregation == \at(queue_context->Priority.Actions.actions, Pre);
    // assert priority_aggregation != NULL;
#endif
    break;
  case PRIORITY_ACTION_REMOVE:
#if defined(RTEMS_SMP)
    _Priority_Extract(
        priority_aggregation,
        priority_action_node,
        &queue_context->Priority.Actions,
        _Thread_Priority_action_remove,
        _Thread_Priority_action_change,
        the_thread);
#else
    _Priority_Extract_non_empty(
        priority_aggregation,
        priority_action_node,
        &queue_context->Priority.Actions,
        _Thread_Priority_action_change,
        NULL);
#endif
    break;
  default:
    _Assert(priority_action_type == PRIORITY_ACTION_CHANGE);
    _Priority_Changed(
        priority_aggregation,
        priority_action_node,
        prepend_it,
        &queue_context->Priority.Actions,
        _Thread_Priority_action_change,
        NULL);
    break;
  }
  
  priority_aggregation = next_aggregation;
  //} while (_Priority_Actions_is_valid(priority_aggregation));
  } while (false);
  
  if (!_Priority_Actions_is_empty(&queue_context->Priority.Actions))
  {

    _Thread_queue_Context_add_priority_update(queue_context, the_thread);

    //@ calls _Thread_queue_Do_nothing_priority_actions;
    (*operations->priority_actions)(
        queue,
        &queue_context->Priority.Actions);
    // assert \valid(&queue_context->Priority.Actions);
  }
  // assert \valid(&queue_context->Priority.Actions);
}

void _Thread_Priority_perform_actions(
    Thread_Control *start_of_path,
    Thread_queue_Context *queue_context)
{
  Thread_Control *the_thread;
  size_t update_count;

  _Assert(start_of_path != NULL);

  /*
   * This function is tricky on SMP configurations.  Please note that we do not
   * use the thread queue path available via the thread queue context.  Instead
   * we directly use the thread wait information to traverse the thread queue
   * path.  Thus, we do not necessarily acquire all thread queue locks on our
   * own.  In case of a deadlock, we use locks acquired by other processors
   * along the path.
   */

  the_thread = start_of_path;
  update_count = _Thread_queue_Context_save_priority_updates(queue_context);

  while (true)
  {
    Thread_queue_Queue *queue;

    queue = the_thread->Wait.queue;

    _Thread_Priority_do_perform_actions(
        the_thread,
        queue,
        the_thread->Wait.operations,
        false,
        queue_context);

    if (_Priority_Actions_is_empty(&queue_context->Priority.Actions))
    {
      return;
    }

    _Assert(queue != NULL);
    the_thread = queue->owner;
    _Assert(the_thread != NULL);

    /*
     * In case the priority action list is non-empty, then the current thread
     * is enqueued on a thread queue.  There is no need to notify the scheduler
     * about a priority change, since it will pick up the new priority once it
     * is unblocked.  Restore the previous set of threads bound to update the
     * priority.
     */
    _Thread_queue_Context_restore_priority_updates(
        queue_context,
        update_count);
  }
}

/*@
  requires \valid(the_thread);
  requires \valid(the_thread->Wait.queue);
  requires \valid(the_thread->Wait.operations);
  requires \valid(the_thread->Scheduler.nodes);
  requires \valid(priority_action_node);
  requires \valid(queue_context);
  requires \valid(g_min_priority_node);
  requires the_thread->Scheduler.nodes;
  requires priority_action_type \in {PRIORITY_ACTION_ADD, PRIORITY_ACTION_REMOVE, PRIORITY_ACTION_CHANGE};
  requires \valid(queue_context->Priority.update[0]);
  requires queue_context->Priority.update_count ≡ 0;
  requires (the_thread->Wait.operations)->priority_actions == _Thread_queue_Do_nothing_priority_actions;
  requires \valid(g_scheduler_node_of_wait_priority_node);

  requires \separated(      
    the_thread,
    queue_context,
    the_thread->Scheduler.nodes,
    the_thread->Wait.operations,
    the_thread->Wait.queue
  );

  requires \separated(
      &the_thread->Scheduler.nodes->Wait.Priority.Node.priority,
      &g_scheduler_node_of_wait_priority_node->Priority.value,
      &g_min_priority_node->priority,
      &priority_action_node->priority,
      &queue_context->Priority.update_count
  );

  behavior priority_add_new_minimum:
    assumes priority_action_type == PRIORITY_ACTION_ADD;
    assumes g_new_minimum;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      the_thread->Scheduler.nodes->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count,
      queue_context->Priority.Actions.actions, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (\old(priority_action_node->priority) | 1);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == \old(priority_action_node->priority);  
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;  
  
  behavior priority_add_no_new_minimum:
    assumes !g_new_minimum;
    assumes priority_action_type == PRIORITY_ACTION_ADD;
    assigns 
       queue_context->Priority.Actions.actions,
       the_thread->Scheduler.nodes->Wait.Priority.Action.type,
       the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == \old(g_scheduler_node_of_wait_priority_node->Priority.value);
  
  behavior priority_remove_new_minimum:
    assumes priority_action_type == PRIORITY_ACTION_REMOVE;
    assumes priority_action_node->priority < g_min_priority_node->priority;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count, 
      queue_context->Priority.Actions.actions,
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (g_min_priority_node->priority | 0);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;
  
  behavior priority_remove_no_new_minimum:
    assumes priority_action_type == PRIORITY_ACTION_REMOVE;
    assumes !(priority_action_node->priority < g_min_priority_node->priority);
    assigns 
      queue_context->Priority.Actions.actions,
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == \old(g_scheduler_node_of_wait_priority_node->Priority.value);
  
  behavior priority_change_new_minimum:
    assumes priority_action_type == PRIORITY_ACTION_CHANGE;
    assumes the_thread->Scheduler.nodes->Wait.Priority.Node.priority != g_min_priority_node->priority;
    assumes !prepend_it;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count, 
      queue_context->Priority.Actions.actions, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (g_min_priority_node->priority | 1);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_change_new_minimum_prepend:
    assumes priority_action_type == PRIORITY_ACTION_CHANGE;
    assumes the_thread->Scheduler.nodes->Wait.Priority.Node.priority != g_min_priority_node->priority;
    assumes prepend_it;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count, 
      queue_context->Priority.Actions.actions,
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (g_min_priority_node->priority | 0);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_change_no_new_minimum:
    assumes priority_action_type == PRIORITY_ACTION_CHANGE;
    assumes the_thread->Scheduler.nodes->Wait.Priority.Node.priority == g_min_priority_node->priority;
    assigns 
       queue_context->Priority.Actions.actions,
       the_thread->Scheduler.nodes->Wait.Priority.Action.type,
       the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == \old(g_scheduler_node_of_wait_priority_node->Priority.value);

  complete behaviors;
  disjoint behaviors;
 */
static void _Thread_Priority_apply(
    Thread_Control *the_thread,
    Priority_Node *priority_action_node,
    Thread_queue_Context *queue_context,
    bool prepend_it,
    Priority_Action_type priority_action_type)
{
  Scheduler_Node *scheduler_node;
  Thread_queue_Queue *queue;

  scheduler_node = _Thread_Scheduler_get_home_node(the_thread);

  _Priority_Actions_initialize_one(
      &queue_context->Priority.Actions,
      &scheduler_node->Wait.Priority,
      priority_action_node,
      priority_action_type);

  queue = the_thread->Wait.queue;

  _Thread_Priority_do_perform_actions(
      the_thread,
      queue,
      the_thread->Wait.operations,
      prepend_it,
      queue_context);
  //@ assert queue_context->Priority.Actions.actions == NULL;

  if (!_Priority_Actions_is_empty(&queue_context->Priority.Actions))
  {
    
#if defined(RTEMS_SMP)
    _Thread_queue_Path_acquire_critical(queue, the_thread, queue_context);
#endif
    _Thread_Priority_perform_actions(queue->owner, queue_context);
#if defined(RTEMS_SMP)
    _Thread_queue_Path_release_critical(queue_context);
#endif
  }
}

/*@
  requires \valid(the_thread->Wait.queue);
  requires \valid(the_thread->Wait.operations);
  requires \valid(the_thread->Scheduler.nodes);
  requires \valid(the_thread); 
  requires \valid(priority_node);
  requires \valid(queue_context);
  requires \valid(g_scheduler_node_of_wait_priority_node) && \valid(g_min_priority_node);
  requires \valid(queue_context->Priority.update[0]);
  requires queue_context->Priority.update_count == 0;
  requires the_thread->Wait.operations->priority_actions == 
    _Thread_queue_Do_nothing_priority_actions;

  requires \separated(      
    queue_context,
    the_thread->Scheduler.nodes,
    the_thread->Wait.operations,
    the_thread->Wait.queue,
    the_thread
  );

  requires 
    \separated(
      &the_thread->Scheduler.nodes->Wait.Priority.Node.priority,
      &g_scheduler_node_of_wait_priority_node->Priority.value,
      &g_min_priority_node->priority,
      &priority_node->priority,
      &queue_context->Priority.update_count
    );
 
  ensures queue_context->Priority.Actions.actions == NULL;

  behavior priority_add_new_minimum:
    assumes g_new_minimum;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      the_thread->Scheduler.nodes->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count,
      queue_context->Priority.Actions.actions, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (\old(priority_node->priority) | 1);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == \old(priority_node->priority);  
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;  
  
  behavior priority_add_no_new_minimum:
    assumes !g_new_minimum;
    assigns 
       queue_context->Priority.Actions.actions,
       the_thread->Scheduler.nodes->Wait.Priority.Action.type,
       the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == \old(g_scheduler_node_of_wait_priority_node->Priority.value);
*/
void _Thread_Priority_add(
    Thread_Control *the_thread,
    Priority_Node *priority_node,
    Thread_queue_Context *queue_context)
{
  _Thread_Priority_apply(
      the_thread,
      priority_node,
      queue_context,
      false,
      PRIORITY_ACTION_ADD);
}

/*@
  requires \valid(the_thread->Wait.queue);
  requires \valid(the_thread->Wait.operations);
  requires \valid(the_thread->Scheduler.nodes);
  requires \valid(the_thread); 
  requires \valid(priority_node);
  requires \valid(queue_context);
  requires \valid(g_scheduler_node_of_wait_priority_node) && \valid(g_min_priority_node);
  requires \valid(queue_context->Priority.update[0]);
  requires queue_context->Priority.update_count == 0;
  requires the_thread->Wait.operations->priority_actions == 
    _Thread_queue_Do_nothing_priority_actions;

  requires \separated(      
    queue_context,
    the_thread->Scheduler.nodes,
    the_thread->Wait.operations,
    the_thread->Wait.queue,
    the_thread
  );

  requires 
    \separated(
      &the_thread->Scheduler.nodes->Wait.Priority.Node.priority,
      &g_scheduler_node_of_wait_priority_node->Priority.value,
      &g_min_priority_node->priority,
      &priority_node->priority,
      &queue_context->Priority.update_count
    );
 
  ensures queue_context->Priority.Actions.actions == NULL;
  
  behavior priority_remove_new_minimum:
    assumes priority_node->priority < g_min_priority_node->priority;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count, 
      queue_context->Priority.Actions.actions,
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (g_min_priority_node->priority | 0);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;
  
  behavior priority_remove_no_new_minimum:
    assumes !(priority_node->priority < g_min_priority_node->priority);
    assigns 
      queue_context->Priority.Actions.actions,
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == \old(g_scheduler_node_of_wait_priority_node->Priority.value);
  complete behaviors;
  disjoint behaviors;  
*/
void _Thread_Priority_remove(
    Thread_Control *the_thread,
    Priority_Node *priority_node,
    Thread_queue_Context *queue_context)
{
  _Thread_Priority_apply(
      the_thread,
      priority_node,
      queue_context,
      true,
      PRIORITY_ACTION_REMOVE);
}

/*@
  requires \valid(the_thread->Wait.queue);
  requires \valid(the_thread->Wait.operations);
  requires \valid(the_thread->Scheduler.nodes);
  requires \valid(the_thread); 
  requires \valid(priority_node);
  requires \valid(queue_context);
  requires \valid(g_scheduler_node_of_wait_priority_node) && \valid(g_min_priority_node);
  requires \valid(queue_context->Priority.update[0]);
  requires queue_context->Priority.update_count == 0;
  requires the_thread->Wait.operations->priority_actions == 
    _Thread_queue_Do_nothing_priority_actions;

  requires \separated(      
    queue_context,
    the_thread->Scheduler.nodes,
    the_thread->Wait.operations,
    the_thread->Wait.queue,
    the_thread
  );

  requires 
    \separated(
      &the_thread->Scheduler.nodes->Wait.Priority.Node.priority,
      &g_scheduler_node_of_wait_priority_node->Priority.value,
      &g_min_priority_node->priority,
      &priority_node->priority,
      &queue_context->Priority.update_count
  );

behavior priority_change_new_minimum:
    assumes the_thread->Scheduler.nodes->Wait.Priority.Node.priority != g_min_priority_node->priority;
    assumes !prepend_it;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count, 
      queue_context->Priority.Actions.actions,
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (g_min_priority_node->priority | 1);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_change_new_minimum_prepend:
    assumes the_thread->Scheduler.nodes->Wait.Priority.Node.priority != g_min_priority_node->priority;
    assumes prepend_it;
    assigns 
      g_scheduler_node_of_wait_priority_node->Priority.value, 
      \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority,
      queue_context->Priority.update[0], 
      queue_context->Priority.update_count, 
      queue_context->Priority.Actions.actions,
      the_thread->Scheduler.nodes->Wait.Priority.Action.type, 
      the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == (g_min_priority_node->priority | 0);
    ensures \old(the_thread->Scheduler.nodes)->Wait.Priority.Node.priority == g_min_priority_node->priority;
    ensures queue_context->Priority.update[0] == the_thread;
    ensures queue_context->Priority.update_count == 1;

  behavior priority_change_no_new_minimum:
    assumes the_thread->Scheduler.nodes->Wait.Priority.Node.priority == g_min_priority_node->priority;
    assigns 
       queue_context->Priority.Actions.actions,
       the_thread->Scheduler.nodes->Wait.Priority.Action.type,
       the_thread->Scheduler.nodes->Wait.Priority.Action.node;
    ensures g_scheduler_node_of_wait_priority_node->Priority.value == \old(g_scheduler_node_of_wait_priority_node->Priority.value);

  complete behaviors;
  disjoint behaviors;  
*/
void _Thread_Priority_changed(
    Thread_Control *the_thread,
    Priority_Node *priority_node,
    bool prepend_it,
    Thread_queue_Context *queue_context)
{
  _Thread_Priority_apply(
      the_thread,
      priority_node,
      queue_context,
      prepend_it,
      PRIORITY_ACTION_CHANGE);
}

void _Thread_Priority_replace(
    Thread_Control *the_thread,
    Priority_Node *victim_node,
    Priority_Node *replacement_node)
{
  Scheduler_Node *scheduler_node;

  scheduler_node = _Thread_Scheduler_get_home_node(the_thread);
  _Priority_Replace(
      &scheduler_node->Wait.Priority,
      victim_node,
      replacement_node);
}

/*@
  requires \valid(queue_context);
  requires queue_context->Priority.update_count == 1;
  requires \valid(queue_context->Priority.update[0]);

  
*/
void _Thread_Priority_update(Thread_queue_Context *queue_context)
{
  size_t i;
  size_t n;

  n = queue_context->Priority.update_count;

  /*
   * Update the priority of all threads of the set.  Do not care to clear the
   * set, since the thread queue context will soon get destroyed anyway.
   */
  for (i = 0; i < n; ++i)
  {
    Thread_Control *the_thread;
    ISR_lock_Context lock_context;

    the_thread = queue_context->Priority.update[i];
    _Thread_State_acquire(the_thread, &lock_context);
    _Scheduler_Update_priority(the_thread);
    _Thread_State_release(the_thread, &lock_context);
  }
}

#if defined(RTEMS_SMP)
void _Thread_Priority_and_sticky_update(
    Thread_Control *the_thread,
    int sticky_level_change)
{
  ISR_lock_Context lock_context;

  _Thread_State_acquire(the_thread, &lock_context);
  _Scheduler_Priority_and_sticky_update(
      the_thread,
      sticky_level_change);
  _Thread_State_release(the_thread, &lock_context);
}
#endif