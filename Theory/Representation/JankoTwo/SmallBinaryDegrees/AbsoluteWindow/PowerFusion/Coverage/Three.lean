module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Reduction
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.Sylow
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.OneCentralizer
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Three.SevenCentralizer

/-!
# The cubic branch of Hall--Janko representative coverage

The certified Sylow subgroup proves that every element of order three belongs
to the class of representative 1 or 7. For an odd-order element whose order is
divisible by three, its cubic-order power places the original element in one
of these two centralizers, after an actual carrier conjugation.

The first centralizer has a certified exhaustive enumeration, including mixed
orders such as 15. In the second, the action on four fixed points and the
pointwise-fixer certificate force every odd order to divide nine, so Sylow
fusion supplies coverage. The final theorem discharges both centralizer
premises and covers every odd-order element whose order is divisible by three.
Source: the ATLAS `J2G1-p100B0` normal forms and the certified carrier order.
-/

namespace Sporadic.LeechRelated.J2.PowerFusionCertificate

private theorem covered_odd_of_conjugate_centralizer {u x g : Carrier}
    (hcover : ∀ z : Carrier, z ∈ Subgroup.centralizer ({x} : Set Carrier) →
      ¬2 ∣ orderOf z → 3 ∣ orderOf z → ∃ i : Fin 21, IsConj (representative i) z)
    (hconj : IsConj u x) (hcomm : Commute g u)
    (h2 : ¬2 ∣ orderOf g) (h3 : 3 ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hcx : MulAut.conj c u = x := hc
  have hcg : Commute (MulAut.conj c g) x := by
    rw [← hcx]
    exact hcomm.map (MulAut.conj c)
  have h2' : ¬2 ∣ orderOf (MulAut.conj c g) := by
    rw [(MulAut.conj c).orderOf_eq]
    exact h2
  have h3' : 3 ∣ orderOf (MulAut.conj c g) := by
    rw [(MulAut.conj c).orderOf_eq]
    exact h3
  obtain ⟨i, hi⟩ := hcover (MulAut.conj c g)
    (Subgroup.mem_centralizer_singleton_iff.mpr hcg.eq) h2' h3'
  exact ⟨i, hi.trans (isConj_iff.mpr ⟨c, rfl⟩).symm⟩

/-- Assembly of the entire odd cubic branch, including composite orders, from
coverage of odd orders divisible by three in the two actual cubic centralizers. The centralizer
premises must be discharged before this gives unconditional branch coverage. -/
public theorem covered_odd_of_three_dvd_of_centralizers
    (h1 : ∀ z : Carrier,
      z ∈ Subgroup.centralizer ({representative 1} : Set Carrier) →
      ¬2 ∣ orderOf z → 3 ∣ orderOf z → ∃ i : Fin 21, IsConj (representative i) z)
    (h7 : ∀ z : Carrier,
      z ∈ Subgroup.centralizer ({representative 7} : Set Carrier) →
      ¬2 ∣ orderOf z → 3 ∣ orderOf z → ∃ i : Fin 21, IsConj (representative i) z)
    (g : Carrier) (h2 : ¬2 ∣ orderOf g) (h3 : 3 ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  have hp : orderOf (g ^ (orderOf g / 3)) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' h3
  rcases three_fusion (g ^ (orderOf g / 3)) hp with h | h
  · exact covered_odd_of_conjugate_centralizer h1 h.symm (Commute.self_pow g _) h2 h3
  · exact covered_odd_of_conjugate_centralizer h7 h.symm (Commute.self_pow g _) h2 h3

/-- Every odd-order element whose order is divisible by three is conjugate,
inside the literal Hall--Janko carrier, to a designated representative.
Both cubic centralizer coverage premises are discharged, including mixed orders. -/
public theorem covered_odd_of_three_dvd (g : Carrier)
    (h2 : ¬2 ∣ orderOf g) (h3 : 3 ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g :=
  covered_odd_of_three_dvd_of_centralizers
    covered_odd_three_centralizer_one covered_odd_three_centralizer_seven g h2 h3

end Sporadic.LeechRelated.J2.PowerFusionCertificate
