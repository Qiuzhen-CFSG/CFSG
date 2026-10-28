module

public import Theory.GroupTheory.NormalAbelianSylowCentralizer
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Centralizers detected inside a Sylow subgroup

Let U be a normal subgroup of a finite group with trivial p'-core. If its
centralizer meets a Sylow p-subgroup in U, its full centralizer is U.
Indeed U is a central Sylow subgroup of the normal centralizer. Burnside
transfer kills its prime-to-p complement, whose characteristic core would
otherwise give a nontrivial ambient p'-core.

This is the centralizer-kernel argument used for elementary subgroups in
local characteristic-p analysis. The transfer input is Burnside's normal
p-complement theorem from `Mathlib.GroupTheory.Transfer`.
-/

namespace Sylow

/-- A normal subgroup self-centralizing in a Sylow subgroup is fully
self-centralizing when the ambient prime-complement core is trivial. -/
public theorem centralizer_eq_of_inf_eq_of_pPrimeCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (U : Subgroup G) [U.Normal]
    (hself : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = U)
    (hcore : pPrimeCore p G = ⊥) : Subgroup.centralizer (U : Set G) = U := by
  let C := Subgroup.centralizer (U : Set G)
  let : C.Normal := Subgroup.normal_centralizer
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal C
  have hTC : Subgroup.normalizer (T : Set C) ≤ Subgroup.centralizer (T : Set C) := by
    intro c _
    apply Subgroup.mem_centralizer_iff.mpr
    intro t ht
    apply Subtype.ext
    have htU : (t : G) ∈ U := hself.le ⟨by
      change t ∈ (S : Subgroup G).subgroupOf C
      rwa [← hT], t.property⟩
    exact Subgroup.mem_centralizer_iff.mp c.property t htU
  have hmap : (pPrimeCore p C).map C.subtype = ⊥ :=
    pPrimeCore_eq_bot_iff.mp hcore _ inferInstance
      (Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ C.subtype)
        pPrimeCore_coprime_card)
  have hcoreC : pPrimeCore p C = ⊥ :=
    Subgroup.map_injective (f := C.subtype) Subtype.val_injective
      (by simpa only [Subgroup.map_bot] using hmap)
  let f := MonoidHom.transferSylow T hTC
  have hfker : f.ker = ⊥ := by
    apply bot_unique
    rw [← hcoreC]
    exact le_sSup ⟨inferInstance,
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (MonoidHom.not_dvd_card_ker_transferSylow T hTC)⟩
  have hCp : IsPGroup p C := T.isPGroup'.of_injective f
    ((MonoidHom.ker_eq_bot_iff f).mp hfker)
  apply le_antisymm
  · intro c hc
    exact hself.le ⟨hCp.le_sylow_of_normal S hc, hc⟩
  · exact hself.ge.trans inf_le_right

/-- A Sylow-centralizer equality upgrades to the full centralizer when the
Sylow normalizes the subgroup and its normalizer has trivial p'-core. -/
public theorem centralizer_eq_of_inf_eq_of_normalizer_pPrimeCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (U : Subgroup G)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G))
    (hself : (S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = U)
    (hcore : pPrimeCore p (Subgroup.normalizer (U : Set G)) = ⊥) :
    Subgroup.centralizer (U : Set G) = U := by
  let N := Subgroup.normalizer (U : Set G)
  let V := U.subgroupOf N
  let T := S.subtype hSN
  have hcentral : Subgroup.centralizer (V : Set N) =
      (Subgroup.centralizer (U : Set G)).subgroupOf N := by
    ext n
    simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h u hu
      exact congrArg Subtype.val (h ⟨u, U.le_normalizer hu⟩ hu)
    · intro h u hu
      exact Subtype.ext (h u hu)
  have hselfN : (T : Subgroup N) ⊓ Subgroup.centralizer (V : Set N) = V := by
    rw [hcentral]
    ext n
    change ((n : G) ∈ (S : Subgroup G) ∧
      (n : G) ∈ Subgroup.centralizer (U : Set G)) ↔ (n : G) ∈ U
    exact SetLike.ext_iff.mp hself (n : G)
  have h := T.centralizer_eq_of_inf_eq_of_pPrimeCore_eq_bot V hselfN hcore
  rw [hcentral] at h
  apply le_antisymm
  · intro c hc
    exact h.le (show (⟨c, Subgroup.centralizer_le_normalizer _ hc⟩ : N) ∈
      (Subgroup.centralizer (U : Set G)).subgroupOf N from hc)
  · exact hself.ge.trans inf_le_right

end Sylow
