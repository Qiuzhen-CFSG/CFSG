module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsPointCore

/-!
# Aligning the actual paired Sylow inside the singular centralizer

Both full ambient Sylow subgroups lie in the centralizer of the same
original singular point. Conjugacy inside that centralizer sends P to
the unchanged T and sends the actual original V into T. No normality
of V in P is needed. The transported two-point orbit has displacements
in the singular line, so the original form-preserving action forces
both transported involutions to centralize V and hence to belong to Q.

Source: the original paired HS configuration in the analysis of
Aschbacher--Smith 12.6.12, retaining the full Sylow and original module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem pair_orbit_of_index_two (S P : Subgroup G)
    (hi : S.relIndex P = 2) (u w t : G)
    (hu : u ∈ centralizer (S : Set G)) (hw : w ∈ centralizer (S : Set G))
    (ht : t ∈ P) (htS : t ∉ S) (hswap : MulAut.conj t u = w) :
    ∀ x ∈ P, MulAut.conj x u = u ∨ MulAut.conj x u = w := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact .inl (mul_inv_eq_iff_eq_mul.mpr (hu x hxS))
  · have hxt : x*t⁻¹ ∈ S :=
      ((S.subgroupOf P).mul_mem_iff_of_index_two hi).mpr
        (show (⟨x,hx⟩ : P) ∈ S.subgroupOf P ↔
          (⟨t⁻¹,P.inv_mem ht⟩ : P) ∈ S.subgroupOf P from by
          change x ∈ S ↔ t⁻¹ ∈ S
          simp only [inv_mem_iff,hxS,htS])
    right
    calc
      MulAut.conj x u = MulAut.conj (x*t⁻¹) (MulAut.conj t u) := by
        simp only [MulAut.conj_apply,mul_inv_rev,inv_inv]
        group
      _ = w := by rw [hswap]; exact mul_inv_eq_iff_eq_mul.mpr (hw _ hxt)

omit [Finite G] in
private theorem involution_zpowers_cases (a x : G) (ha1 : a ≠ 1)
    (ha2 : a^2=1) (hx : x ∈ zpowers a) : x=1 ∨ x=a := by
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
  have hr : a^n=a^(n%2) := by
    simpa only [orderOf_eq_prime ha2 ha1,Nat.cast_ofNat] using
      (zpow_mod_orderOf a n).symm
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hr,h]; simp
  · right; rw [hr,h]; simp

omit [IsElementaryAbelian 2 V] in
private theorem actual_sylow_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = Q T L := by
  apply le_antisymm
  · intro x hx
    exact H.join_centralizer_eq_core hTV ▸ ⟨mem_sup_right hx.1,hx.2⟩
  · intro x hx
    exact ⟨(Q_le_Tv H.chosen (1:V) hx).1,H.chosen.core_centralizes hx⟩

/-- A two-point Sylow orbit whose product is the original singular point
lies in the original full core Q, by the actual form-preserving action. -/
theorem SourceHypothesis.singular_pair_orbit_mem_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hZ : ZV L V = ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (z : V) (hz : z ≠ 1) (hs : ¬ D.Nonsingular z)
    (a : G) (haT : a ∈ (T : Subgroup G)) (ha1 : a ≠ 1) (ha2 : a^2=1)
    (horbit : ∀ x ∈ (T : Subgroup G),
      MulAut.conj x a = a ∨ MulAut.conj x a = (z : G)*a) :
    a ∈ Q T L := by
  let E := D.fullSetup hZ T z
  have hline : ⁅V,zpowers a⁆ ≤ E.V₁ := by
    apply commutator_le.mpr
    intro x hx b hb
    rcases involution_zpowers_cases a b ha1 ha2 hb with hb1 | hba
    · rw [hb1]
      simp
    · rw [hba]
      rcases horbit x (H.chosen.le_sylow hx) with he | he
      · have hc : ⁅x,a⁆=1 := by
          change (MulAut.conj x a)*a⁻¹=1
          rw [he,mul_inv_cancel]
        rw [hc]
        exact E.V₁.one_mem
      · have hc : ⁅x,a⁆=(z:G) := by
          change (MulAut.conj x a)*a⁻¹=(z:G)
          rw [he,mul_inv_cancel_right]
        rw [hc]
        exact mem_zpowers _
  obtain ⟨f,_,hf⟩ := H.original_normalizer_permutation_action D hZ hTV
  have hsing : BinaryPermutation.TerminalOrthogonal.Eight.form (E.coordinates E.z).toAdd=0 := by
    apply not_ne_iff.mp
    exact fun hn => hs ((D.fullCoordinates_nonsingular_iff hZ z).mp hn)
  have hzero := E.commutator_eq_bot_of_singular_line hz hsing
    (fun n => ⟨f n,hf n⟩) (zpowers a) (zpowers_le.mpr (hTV haT))
    (by rwa [commutator_comm])
  have hac : a ∈ centralizer (V : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hzero (mem_zpowers a)
  exact actual_sylow_centralizer H hTV ▸ ⟨haT,hac⟩

/-- Align the constructed full Sylow with the unchanged original T in
the same singular centralizer. Every P-normalized subgroup is transported
to a T-normalized subgroup, and the original pair returns into Q. -/
theorem SourceHypothesis.original_hs_pair_sylow_alignment
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (hZ : ZV L V = ⊥)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (u w : V) (hu : D.Nonsingular u)
    (huw : u ≠ w) (hs : ¬ D.Nonsingular (u*w))
    (hTz : (T : Subgroup G) ≤ Gv ((u*w : V) : G))
    (P : Sylow 2 G) (hVP : V ≤ (P : Subgroup G))
    (hPz : (P : Subgroup G) ≤ Gv ((u*w : V) : G))
    (S : Subgroup G)
    (hi : S.relIndex (P : Subgroup G)=2)
    (huS : (u:G) ∈ centralizer (S : Set G))
    (hwS : (w:G) ∈ centralizer (S : Set G))
    (t : G) (ht : t ∈ (P : Subgroup G)) (htS : t ∉ S)
    (hswap : MulAut.conj t (u:G)=(w:G)) :
    ∃ c : Gv ((u*w : V) : G),
      (P : Subgroup G).map (MulAut.conj (c:G)).toMonoidHom = (T : Subgroup G) ∧
      V.map (MulAut.conj (c:G)).toMonoidHom ≤ (T : Subgroup G) ∧
      MulAut.conj (c:G) (u:G) ∈ Q T L ∧
      MulAut.conj (c:G) (w:G) ∈ Q T L ∧
      MulAut.conj (c:G) (u:G) * MulAut.conj (c:G) (w:G) = ((u*w : V):G) ∧
      (∀ J : Subgroup G, (P : Subgroup G) ≤ normalizer (J : Set G) →
        (T : Subgroup G) ≤ normalizer (J.map (MulAut.conj (c:G)).toMonoidHom : Set G)) := by
  let z : V := u*w
  have hz : z ≠ 1 := by
    intro he
    have hu2 : u*u=1 := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul,Subgroup.coe_one,pow_two] using
        (elemPow_eq_one_of_isElementaryAbelian (p:=2) (u:G) u.property)
    have hw' : w=u := by
      calc
        w = u*(u*w) := by rw [←mul_assoc,hu2,one_mul]
        _ = u := by rw [show u*w=1 from he,mul_one]
    exact huw hw'.symm
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq (Gv (z:G)) (P.subtype hPz) (T.subtype hTz)
  have hPT : (P : Subgroup G).map (MulAut.conj (c:G)).toMonoidHom = (T : Subgroup G) := by
    have hh := congrArg (fun R : Sylow 2 (Gv (z:G)) =>
      (R : Subgroup (Gv (z:G))).map (Gv (z:G)).subtype) hc
    rw [Sylow.smul_subtype,Sylow.coe_subtype,Sylow.coe_subtype] at hh
    change (((P : Subgroup G).map (MulAut.conj (c:G)).toMonoidHom).subgroupOf (Gv (z:G))).map (Gv (z:G)).subtype =
      ((T : Subgroup G).subgroupOf (Gv (z:G))).map (Gv (z:G)).subtype at hh
    have hmap : (P : Subgroup G).map (MulAut.conj (c:G)).toMonoidHom ≤ Gv (z:G) := by
      exact Sylow.smul_le hPz c
    rw [map_subgroupOf_eq_of_le hmap,map_subgroupOf_eq_of_le hTz] at hh
    exact hh
  let a := MulAut.conj (c:G)
  have haz : a (z:G)=(z:G) := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp c.property)
  have hprod : a (u:G)*a (w:G)=(z:G) := by rw [←map_mul]; exact haz
  have hu2 : (u:G)^2=1 := elemPow_eq_one_of_isElementaryAbelian _ u.property
  have hwa : a (w:G)=(z:G)*a (u:G) := by
    rw [←hprod]
    rw [←map_mul,←map_mul]
    apply congrArg a
    exact congrArg (fun x : V => (x:G)) (show w=u*w*u from by
      rw [mul_assoc,mul_comm w u,←mul_assoc]
      have he : u*u=1 := Subtype.ext (by simpa only [Subgroup.coe_mul,Subgroup.coe_one,pow_two] using hu2)
      rw [he,one_mul])
  have horbit := pair_orbit_of_index_two S P hi (u:G) (w:G) t huS hwS ht htS hswap
  have haorbit : ∀ x ∈ (T : Subgroup G),
      MulAut.conj x (a (u:G))=a (u:G) ∨
      MulAut.conj x (a (u:G))=(z:G)*a (u:G) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hPT.ge hx
    have hh : MulAut.conj (a y) (a (u:G))=a (MulAut.conj y (u:G)) := by
      simp only [MulAut.conj_apply,map_mul,map_inv]
    change MulAut.conj (a y) (a (u:G))=a (u:G) ∨
      MulAut.conj (a y) (a (u:G))=(z:G)*a (u:G)
    rw [hh]
    rcases horbit y hy with he | he
    · exact .inl (congrArg a he)
    · exact .inr ((congrArg a he).trans hwa)
  have haQ : a (u:G) ∈ Q T L := H.singular_pair_orbit_mem_core D hZ hTV z hz hs
    (a (u:G)) (hPT ▸ mem_map_of_mem a.toMonoidHom (hVP u.property))
    (fun he => nonsingular_ne_one D hu (Subtype.ext (a.injective (he.trans a.map_one.symm))))
    (by rw [←map_pow,hu2,map_one]) haorbit
  have hzQ : (z:G) ∈ Q T L := actual_sylow_centralizer H hTV ▸
    ⟨H.chosen.le_sylow z.property,(le_centralizer V) z.property⟩
  refine ⟨c,hPT,hPT ▸ map_mono hVP,haQ,?_,hprod,?_⟩
  · rw [hwa]
    exact (Q T L).mul_mem hzQ haQ
  · intro J hJ
    rw [←hPT]
    exact (map_mono hJ).trans (J.le_normalizer_map _)

end CFSG.Quasithin.Chapter12.Section06
