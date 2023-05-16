#include <rtems/score/thread.h>
#include <rtems/score/threadq.h>
#include <rtems/score/priority.h>
#include <rtems/score/watchdog.h>
#include <rtems/score/interr.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>
#include <rtems/score/status.h>
#include <rtems/score/scheduleredf.h>
#include <sys/tree.h>
#include <rtems/score/statesimpl.h>

/*@ ghost 
  extern Priority_Node *g_min_priority_node;
  extern Scheduler_Node *g_scheduler_node_of_wait_priority_node;
  extern Scheduler_EDF_Node *g_min_edf_node;
  extern Scheduler_EDF_Context *g_edf_sched_context;
*/
static void _Thread_Priority_action_change(
  Priority_Aggregation *priority_aggregation,
  bool                  prepend_it,
  Priority_Actions     *priority_actions,
  void                 *arg
);

static void _Thread_Set_scheduler_node_priority(
    Priority_Aggregation *priority_aggregation,
    bool prepend_it);

/*@
  requires \valid(priority_aggregation);
  assigns \nothing;
  ensures \result == g_scheduler_node_of_wait_priority_node;
*/
Scheduler_Node *_Helper_SCHEDULER_NODE_OF_WAIT_PRIORITY_NODE( Priority_Aggregation *priority_aggregation);

/*@
  requires \valid(priority_actions);
  assigns priority_actions->actions;
  ensures priority_actions->actions == NULL;
*/
static void _Thread_queue_Do_nothing_priority_actions(
  Thread_queue_Queue *queue,
  Priority_Actions   *priority_actions
);

/*@
  requires \valid_read(tree);
  assigns \nothing;
  ensures \result == g_min_priority_node;
*/
Priority_Node *_Helper_RBTree_Minimum( const RBTree_Control *tree );

/*@
  requires \valid_read(tree);
  assigns \nothing;
  ensures \result == g_min_edf_node;
*/
Scheduler_EDF_Node *_Helper_RBTree_EDF_Minimum( const RBTree_Control *tree );