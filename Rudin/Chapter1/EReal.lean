import Mathlib
import Rudin.Chapter1.Real


namespace Rudin

namespace EReal

def ExtendedReal := WithBot (WithTop RR)
  deriving Bot, Zero, One, Nontrivial

noncomputable instance : AddMonoid ExtendedReal := inferInstanceAs (AddMonoid (WithBot (WithTop RR)))
noncomputable instance : PartialOrder ExtendedReal := inferInstanceAs (PartialOrder (WithBot (WithTop RR)))
noncomputable instance : AddCommMonoid ExtendedReal := inferInstanceAs (AddCommMonoid (WithBot (WithTop RR)))

instance : ZeroLEOneClass ExtendedReal := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop RR)))

noncomputable instance : LinearOrder ExtendedReal := inferInstanceAs (LinearOrder (WithBot (WithTop RR)))

instance : IsOrderedAddMonoid ExtendedReal := inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop RR)))

instance : IsOrderedAddMonoid ExtendedReal := inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop RR)))

noncomputable instance : AddCommMonoidWithOne ExtendedReal := inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop RR)))

instance : DenselyOrdered ExtendedReal := inferInstanceAs (DenselyOrdered (WithBot (WithTop RR)))

-- todo

end EReal

abbrev EReal := EReal.ExtendedReal
abbrev ERR := EReal.ExtendedReal

end Rudin
