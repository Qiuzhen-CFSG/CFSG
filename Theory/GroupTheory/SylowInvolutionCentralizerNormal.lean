module

public import Theory.GroupTheory.InvolutionPairCentralInvolution
public import Theory.GroupTheory.SylowCentralizerTrivialIntersection

/-!
# Sylow normality from involution centralizers and separated classes

Suppose a Sylow two-subgroup contains the centralizer of each of its
involutions. If two of its involutions are not conjugate in the ambient
group, the Sylow subgroup is normal. An outside involution would be
conjugate to every inside involution: otherwise their dihedral group
provides an involution centralizing both, which forces the outside
involution back into the Sylow subgroup. Thus all involutions lie inside.
Centralizer containment then makes two intersecting Sylow subgroups equal.

The quotient corollary retains the literal quotient map and lifts normality
when its kernel lies in the Sylow subgroup. No solvability assumption is
used. This is the TI conclusion in Parrott, *A characterization of the
Tits' simple group* (1972), printed p. 683.
-/

open Subgroup
open scoped Pointwise

namespace Subgroup

/-- An outside involution is conjugate to every involution in a subgroup
that contains the centralizers of its involutions. -/
public theorem isConj_of_involution_inside_outside
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (hcent : ∀ x ∈ P, orderOf x = 2 → centralizer ({x} : Set G) ≤ P)
    {a b : G} (haP : a ∈ P) (ha : orderOf a = 2)
    (hbP : b ∉ P) (hb : orderOf b = 2) : IsConj a b := by
  by_contra hn
  obtain ⟨w, _, hw, hwa, hwb⟩ :=
    Theory.GroupTheory.exists_central_involution_of_not_isConj a b ha hb hn
  have hwP : w ∈ P := hcent a haP ha (mem_centralizer_singleton_iff.mpr hwa.eq)
  exact hbP (hcent w hwP hw (mem_centralizer_singleton_iff.mpr hwb.symm.eq))

end Subgroup

namespace Sylow

variable {G : Type*} [Group G] [Finite G]

/-- Two separated involution classes force normality under involution
centralizer containment. -/
public theorem normal_of_involution_centralizers_le_of_not_isConj
    (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), orderOf x = 2 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (a b : G) (haP : a ∈ (P : Subgroup G)) (hbP : b ∈ (P : Subgroup G))
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hn : ¬ IsConj a b) :
    (P : Subgroup G).Normal := by
  have hall : ∀ t : G, orderOf t = 2 → t ∈ (P : Subgroup G) := by
    intro t ht
    by_contra htP
    exact hn (((P : Subgroup G).isConj_of_involution_inside_outside hcent haP ha htP ht).trans
      ((P : Subgroup G).isConj_of_involution_inside_outside hcent hbP hb htP ht).symm)
  have hcent' : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      centralizer ({x} : Set G) ≤ (P : Subgroup G) := by
    intro x hx hx1
    have hd : 2 ∣ orderOf x := by
      have hh := P.isPGroup'.dvd_orderOf
        (show (⟨x, hx⟩ : P) ≠ 1 from fun h => hx1 (congrArg Subtype.val h))
      rwa [← Subgroup.orderOf_coe] at hh
    let w := x ^ (orderOf x / 2)
    have hw : orderOf w = 2 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hd
    intro c hc
    exact hcent w ((P : Subgroup G).pow_mem hx _) hw
      (mem_centralizer_singleton_iff.mpr
        (Commute.pow_right (show Commute c x from mem_centralizer_singleton_iff.mp hc) _).eq)
  constructor
  intro x hx g
  let Q : Sylow 2 G := g • P
  have hgaQ : (MulAut.conj g) a ∈ (Q : Subgroup G) := Set.smul_mem_smul_set haP
  have hga : orderOf ((MulAut.conj g) a) = 2 := (MulEquiv.orderOf_eq _ a).trans ha
  have hga1 : (MulAut.conj g) a ≠ 1 := by
    intro he
    simp [he] at hga
  have hQP : Q = P := P.eq_of_inf_ne_bot_of_centralizer_le Q hcent' (by
    intro he
    have hh : (MulAut.conj g) a ∈ (P : Subgroup G) ⊓ (Q : Subgroup G) :=
      ⟨hall _ hga, hgaQ⟩
    rw [he] at hh
    exact hga1 hh)
  have hgx : (MulAut.conj g) x ∈ (Q : Subgroup G) := Set.smul_mem_smul_set hx
  exact hQP ▸ hgx

/-- Normality in the literal quotient lifts through a kernel contained in
the original Sylow subgroup. -/
public theorem normal_of_quotient_involution_centralizers_le_of_not_isConj
    {B : Type*} [Group B] (P : Sylow 2 G) (f : G →* B)
    (hf : Function.Surjective f) (hker : f.ker ≤ (P : Subgroup G))
    (hcent : ∀ x ∈ (P : Subgroup G).map f, orderOf x = 2 →
      centralizer ({x} : Set B) ≤ (P : Subgroup G).map f)
    (a b : B) (haP : a ∈ (P : Subgroup G).map f)
    (hbP : b ∈ (P : Subgroup G).map f)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hn : ¬ IsConj a b) :
    (P : Subgroup G).Normal := by
  let : Finite B := Finite.of_surjective f hf
  let Q : Sylow 2 B := P.mapSurjective hf
  let : ((P : Subgroup G).map f).Normal :=
    Q.normal_of_involution_centralizers_le_of_not_isConj hcent a b haP hbP ha hb hn
  have hc : (((P : Subgroup G).map f).comap f).Normal := inferInstance
  simpa only [comap_map_eq_self hker] using hc

end Sylow
