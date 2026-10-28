module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.Reduction
public import Theory.GroupTheory.ComponentLocalTwelveExclusion.CentralOrbit
public import Theory.Mathieu.M24.Properties.Simplicity

/-!
# Central coordinates for blocks in lifted Mathieu locals

The given intersection identity makes the lifted local invariant under the
stabilizer of its component in S. Its S-conjugates in distinct components
commute. The central-orbit construction therefore maps their join onto a
finite power of the native local subgroup, with central kernel. Two-perfection
puts each block in that join, and its relative subnormality passes to the image.

The proof retains the actual O₂(L) quotient map and allows S to permute
components. Quasisimplicity makes its kernel central; simplicity of the actual
M₂₄ quotient makes the map kill the entire component center. No ambient
normality or trivial-center assumption is used.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526, and the short-group
conditions of C.1.7, printed p.123. The intrinsic local block obstruction is
separate from this transfer.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Restrict the actual component quotient to the full preimage of P. -/
noncomputable def liftProjection (d : SporadicQuotientInput L z .m24)
    (P : Subgroup M24) : lift d P →* P :=
  ((quotientMap d).comp (inclusion (lift_le d P))).codRestrict P (by
    intro x
    rcases x.property with ⟨y, hy, he⟩
    change (y : G) = x.val at he
    have he' : y = inclusion (lift_le d P) x := Subtype.ext he
    change quotientMap d y ∈ P at hy
    change quotientMap d (inclusion (lift_le d P) x) ∈ P
    rw [← he']
    exact hy)

/-- The full preimage maps onto the prescribed native subgroup. -/
theorem liftProjection_surjective (d : SporadicQuotientInput L z .m24)
    (P : Subgroup M24) : Function.Surjective (liftProjection d P) := by
  intro p
  obtain ⟨l, hl⟩ := quotientMap_surjective d p.val
  refine ⟨⟨l, ⟨l, ?_, rfl⟩⟩, ?_⟩
  · change quotientMap d l ∈ P
    rw [hl]
    exact p.property
  · apply Subtype.ext
    change quotientMap d l = p.val
    exact hl

/-- The covering two-kernel is retained and is central in the lifted local. -/
theorem liftProjection_ker_central (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (P : Subgroup M24) :
    (liftProjection d P).ker ≤ center (lift d P) := by
  intro x hx
  have hk : (⟨x.val, lift_le d P x.property⟩ : L) ∈ (quotientMap d).ker :=
    by
      change quotientMap d (inclusion (lift_le d P) x) = 1
      exact congrArg (fun p : P => (p : M24)) hx
  rw [quotientMap_ker] at hk
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (congrArg (fun l : L => (l : G))
    (mem_center_iff.mp (core_le_center h hk) ⟨y.val, lift_le d P y.property⟩))

/-- The component center dies in the actual centerless M₂₄ quotient. -/
theorem liftProjection_kills_center (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (P : Subgroup M24)
    (x : lift d P) (hx : inclusion (lift_le d P) x ∈ center L) :
    liftProjection d P x = 1 := by
  let := h.quasisimple
  let : Group.IsPerfect M24 := Group.IsPerfect.ofSurjective (quotientMap_surjective d)
  let := m24_isSimpleGroup
  have hz : center M24 = ⊥ := by
    rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative M24 (center_eq_top_iff.mp hc)).elim
  have hc : quotientMap d (inclusion (lift_le d P) x) ∈ center M24 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨l, rfl⟩ := quotientMap_surjective d y
    simpa only [map_mul] using congrArg (quotientMap d) (mem_center_iff.mp hx l)
  apply Subtype.ext
  change quotientMap d (inclusion (lift_le d P) x) = 1
  exact mem_bot.mp (hz ▸ hc)

/-- The intersection identity supplies precisely the stabilizer invariance. -/
theorem lift_stabilizer_invariant (d : SporadicQuotientInput L z .m24)
    (A : Subgroup G) (P : Subgroup M24)
    (hinter : L ⊓ localOvergroup d A P = lift d P) :
    A ⊓ normalizer (L : Set G) ≤ normalizer (lift d P : Set G) := by
  intro a ha
  rw [← hinter]
  exact inf_normalizer_le_normalizer_inf
    ⟨ha.2, (localOvergroup d A P).le_normalizer (le_localOvergroup d A P ha.1)⟩

private theorem central_coordinates [Finite G]
    {L K A : Subgroup G} {P B : Type*} [Group P] [Group B]
    (hL : IsComponent G L) (hKL : K ≤ L) (hA : IsPGroup 2 A)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (f : K →* P) (hf : Function.Surjective f) (hcentral : f.ker ≤ center K)
    (hkill : ∀ k : K, inclusion hKL k ∈ center L → f k = 1)
    (hp : IsPPerfect 2 B) (g : B →* (K ⊔ A : Subgroup G))
    (hg : Function.Injective g) (hs : g.range.IsSubnormal) :
    ∃ n : ℕ, ∃ q : B →* (Fin n → P), q.ker ≤ center B ∧ q.range.IsSubnormal := by
  obtain ⟨n, q, hq, hqc⟩ :=
    ComponentLocalTwelveExclusion.central_power_of_component_orbit hL hKL hinv f hf hcentral hkill
  let X := K ⊔ A
  let N := (componentOrbit K A).subgroupOf X
  have hgr : g.range ≤ N := le_local_orbit_of_isPPerfect K A hA g.range
    (hp.of_surjective g.rangeRestrict g.rangeRestrict_surjective)
  let r : B →* N := g.codRestrict N (fun x => hgr ⟨x, rfl⟩)
  have hr : Function.Injective r := fun x y h => hg (congrArg Subtype.val h)
  have hrs : r.range.IsSubnormal := by
    rw [← MonoidHom.subgroupOf_range_eq_of_le g hgr]
    exact hs.subgroupOf
  let e : N ≃* componentOrbit K A := subgroupOfEquivOfLe (componentOrbit_le_sup K A)
  let j := e.toMonoidHom.comp r
  have hj : Function.Injective j := e.injective.comp hr
  refine ⟨n, q.comp j, ?_, ?_⟩
  · intro b hb
    apply mem_center_iff.mpr
    intro c
    apply hj
    simpa only [map_mul] using mem_center_iff.mp (hqc hb) (j c)
  · rw [MonoidHom.range_comp, MonoidHom.range_comp]
    exact (hrs.map e.surjective).map hq

/-- Every short subnormal block has a subnormal image in a finite power of P,
with central kernel on the block itself. -/
theorem block_central_coordinates (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (P : Subgroup M24)
    (hinter : L ⊓ localOvergroup d ((S : Subgroup H).map H.subtype) P = lift d P)
    (B : Subgroup (localOvergroup d ((S : Subgroup H).map H.subtype) P))
    (hB : ChapterC.IsBlock B) :
    ∃ n : ℕ, ∃ q : B →* (Fin n → P), q.ker ≤ center B ∧ q.range.IsSubnormal := by
  let := h.finite
  let K := lift d P
  let A := (S : Subgroup H).map H.subtype
  have hKL : K ≤ L := lift_le d P
  have hKH : K ≤ H := hKL.trans h.component_le
  have hAH : A ≤ H := map_subtype_le _
  let F := K.subgroupOf H
  let C := A.subgroupOf H
  have hFL : F ≤ L.subgroupOf H := subgroupOf_mono H hKL
  have hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G) :=
    lift_stabilizer_invariant d A P hinter
  have hinvH : C ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (F : Set H) := by
    rw [← subgroupOf_normalizer_eq h.component_le, ← subgroupOf_normalizer_eq hKH]
    intro x hx
    exact hinv hx
  let eF : F ≃* K := subgroupOfEquivOfLe hKH
  let eL : L.subgroupOf H ≃* L := subgroupOfEquivOfLe h.component_le
  let fH := (liftProjection d P).comp eF.toMonoidHom
  have hcentralH : fH.ker ≤ center F := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply eF.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      mem_center_iff.mp (liftProjection_ker_central h d P hx) (eF y)
  have hkillH (x : F) (hx : inclusion hFL x ∈ center (L.subgroupOf H)) : fH x = 1 := by
    have hxL : eL (inclusion hFL x) ∈ center L := (centerCongr eL ⟨_, hx⟩).property
    exact liftProjection_kills_center h d P (eF x) hxL
  let eX : (F ⊔ C : Subgroup H) ≃*
      localOvergroup d ((S : Subgroup H).map H.subtype) P :=
    (MulEquiv.subgroupCongr (subgroupOf_sup hKH hAH).symm).trans
      (subgroupOfEquivOfLe (sup_le hKH hAH))
  let g : B →* (F ⊔ C : Subgroup H) := eX.symm.toMonoidHom.comp B.subtype
  have hgs : g.range.IsSubnormal := by
    change (eX.symm.toMonoidHom.comp B.subtype).range.IsSubnormal
    rw [MonoidHom.range_comp, B.range_subtype]
    exact hB.subnormal.map eX.symm.surjective
  have hpA : IsPGroup 2 A := S.isPGroup'.map H.subtype
  exact central_coordinates h.component hFL hpA.comap_subtype hinvH fH
    ((liftProjection_surjective d P).comp eF.surjective) hcentralH hkillH
    hB.short.twoPerfect g (eX.symm.injective.comp B.subtype_injective) hgs
end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

end
