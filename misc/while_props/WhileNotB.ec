pragma Goals:printall.
require import AllCore DBool.
require import Int.


type rrt.

require WhileSplit.
clone import WhileSplit as WS with type rrt <- rrt.


