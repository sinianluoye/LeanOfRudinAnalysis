import Rudin.Tactic
import Rudin.Basic
import Rudin.Chapter1.Set
import Rudin.Chapter1.Field
import Rudin.Chapter1.Ordered
import Rudin.Chapter1.OrderedField
import Rudin.Chapter1.Ratitional

namespace Rudin

structure Cut where
  carrier     : Set ℚ
  nonempty    : carrier.Nonempty
  ne_univ     : carrier ≠ univ

#check Cut.ne_univ

end Rudin
