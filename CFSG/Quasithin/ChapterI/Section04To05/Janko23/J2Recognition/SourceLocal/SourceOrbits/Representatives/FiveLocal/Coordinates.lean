module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.FiveLocal.InternalPairs

/-!
# From a marked component normalizer to the whole pair fixer

Compatible coordinates N_G(L) ≃ L × D₁₀ identify the full ambient
centralizer of L with the second factor. A pair generating L forces its
ambient fixer into this normalizer. Transporting the actual intrinsic
C₂ fixer therefore gives C₂ × D₁₀, with no order-only recognition step.

`ComponentCoordinates` remains an intermediate output to be proved from
47.1–47.2. The final `pairs` constructor also retains the separate root
coordinate obligation. It is not the source theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5, printed p.263.
-/

public section
open Subgroup
open alternatingGroup.FiveLocalGeometry
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
variable {G : Type*} [Group G] [Finite G]

/-- Intermediate ambient output: the marked full normalizer of the chosen
five-local component. This is to be derived from 47.1–47.2, not assumed
as an earlier source theorem. -/
structure ComponentCoordinates (D : Seed G) where
  L : Subgroup G
  equiv : L ≃* A5
  X_le : D.X ≤ L
  normalizerEquiv : normalizer (L : Set G) ≃* (L × DihedralGroup 5)
  on_component : ∀ l : L,
    normalizerEquiv (inclusion L.le_normalizer l) = (l, 1)

private theorem norm_prod_eq {H K : Type*} [Group H] [Group K]
    (P : Subgroup H) (Q : Subgroup K) :
    normalizer (P.prod Q : Set (H × K)) =
      (normalizer (P : Set H)).prod (normalizer (Q : Set K)) := by
  ext g
  simp only [Subgroup.mem_prod, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    constructor
    · intro x
      simpa using h (x, 1)
    · intro x
      simpa using h (1, x)
  · rintro ⟨hP, hQ⟩ ⟨x,y⟩
    exact (hP x).and (hQ y)

namespace ComponentCoordinates
variable {D : Seed G} (O : ComponentCoordinates D)

/-- The actual coordinate embedding of every subgroup of the component. -/
theorem subgroup_coordinates (S : Subgroup G) (hS : S ≤ O.L) :
    (S.subgroupOf (normalizer (O.L : Set G))).map O.normalizerEquiv.toMonoidHom =
      (S.subgroupOf O.L).prod (⊥ : Subgroup (DihedralGroup 5)) := by
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsL : (s : G) ∈ O.L := hS hs
    have hh := O.on_component ⟨s, hsL⟩
    change O.normalizerEquiv s = (⟨s, hsL⟩, 1) at hh
    change O.normalizerEquiv s ∈ _
    rw [hh]
    exact ⟨hs, rfl⟩
  · rintro ⟨ha, hb⟩
    refine ⟨inclusion O.L.le_normalizer a.1, ha, ?_⟩
    change O.normalizerEquiv (inclusion O.L.le_normalizer a.1) = a
    rw [O.on_component]
    exact Prod.ext rfl hb.symm

/-- The second factor is precisely the full ambient centralizer, retaining
its literal embedding, not only its order. -/
theorem centralizer_eq_secondFactor :
    centralizer (O.L : Set G) =
      ((⊥ : Subgroup O.L).prod (⊤ : Subgroup (DihedralGroup 5))).map
        ((normalizer (O.L : Set G)).subtype.comp O.normalizerEquiv.symm.toMonoidHom) := by
  let N := normalizer (O.L : Set G)
  let f := N.subtype.comp O.normalizerEquiv.symm.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp O.normalizerEquiv.symm.injective
  have hcoord (l : O.L) : f (l,1) = l := by
    have h := congrArg (fun x => (O.normalizerEquiv.symm x : G)) (O.on_component l)
    simpa [f] using h.symm
  ext g
  constructor
  · intro hg
    let n : N := ⟨g, centralizer_le_normalizer _ hg⟩
    let a := O.normalizerEquiv n
    have he : f a = g := by simp [f, a, n]
    have hz : a.1 ∈ center O.L := by
      rw [mem_center_iff]
      intro l
      have hc : f ((l,1) * a) = f (a * (l,1)) := by
        simp only [map_mul, hcoord, he]
        exact mem_centralizer_iff.mp hg l l.property
      exact congrArg Prod.fst (hf hc)
    have hz' : a.1 = 1 := by
      have h := (centerCongr O.equiv ⟨a.1, hz⟩).property
      change O.equiv a.1 ∈ center A5 at h
      rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5)), mem_bot] at h
      exact O.equiv.injective (h.trans O.equiv.map_one.symm)
    exact ⟨a, ⟨hz', mem_top _⟩, he⟩
  · rintro ⟨a, ha, rfl⟩
    apply mem_centralizer_iff.mpr
    intro l hl
    have hc : ((⟨l,hl⟩ : O.L),1) * a = a * ((⟨l,hl⟩ : O.L),1) := by
      apply Prod.ext
      · simp [show a.1 = 1 from ha.1]
      · simp
    have he := congrArg f hc
    simpa only [map_mul, hcoord] using he

/-- Both endpoint normalizers lie in the full component normalizer because
these endpoints generate that component. -/
theorem fixer_le_normalizer (P : InternalPairs D O.L) :
    edgeFixer G D.base P.five ≤ normalizer (O.L : Set G) := by
  rw [edgeFixer, D.stabilizer_eq_normalizer, D.stabilizer_eq_normalizer]
  have h := normalizer_inf_normalizer_le_normalizer_sup D.X P.five.val
  rw [P.five_join] at h
  exact h

/-- Compute the whole ambient fixer using the checked intrinsic C₂ fixer. -/
noncomputable def fiveFixerEquiv (P : InternalPairs D O.L) :
    edgeFixer G D.base P.five ≃* (Multiplicative (ZMod 2) × DihedralGroup 5) := by
  let N := normalizer (O.L : Set G)
  let F := edgeFixer G D.base P.five
  let I : Subgroup O.L := normalizer (D.X.subgroupOf O.L : Set O.L) ⊓
    normalizer (P.five.val.subgroupOf O.L : Set O.L)
  have hc : (F.subgroupOf N).map O.normalizerEquiv.toMonoidHom =
      I.prod (⊤ : Subgroup (DihedralGroup 5)) := by
    change ((edgeFixer G D.base P.five).subgroupOf N).map _ = _
    rw [edgeFixer, D.stabilizer_eq_normalizer, D.stabilizer_eq_normalizer]
    change (((normalizer (D.X : Set G)).subgroupOf N) ⊓
      ((normalizer (P.five.val : Set G)).subgroupOf N)).map _ = _
    rw [map_inf _ _ _ O.normalizerEquiv.injective,
      subgroupOf_normalizer_eq (O.X_le.trans O.L.le_normalizer),
      subgroupOf_normalizer_eq (P.five_le.trans O.L.le_normalizer),
      map_equiv_normalizer_eq, map_equiv_normalizer_eq,
      O.subgroup_coordinates D.X O.X_le, O.subgroup_coordinates P.five.val P.five_le,
      norm_prod_eq, norm_prod_eq, normalizer_eq_top_iff.mpr (inferInstance :
        (⊥ : Subgroup (DihedralGroup 5)).Normal)]
    ext x
    simp only [I, mem_inf, mem_prod, mem_top, and_true]
  exact (subgroupOfEquivOfLe (O.fixer_le_normalizer P)).symm.trans
    (((F.subgroupOf N).equivMapOfInjective O.normalizerEquiv.toMonoidHom
      O.normalizerEquiv.injective).trans
      ((MulEquiv.subgroupCongr hc).trans
        ((Subgroup.prodEquiv _ _).trans
          (P.internalFixerEquiv.prodCongr Subgroup.topEquiv))))

/-- Final assembly once the separately proved root identification is supplied.
The additional root premise is an intermediate construction obligation. -/
noncomputable def pairs (P : InternalPairs D O.L) (R : RootPairCoordinates D P.edge) :
    FiveLocalPairs D where
  edge := P.edge
  root := R
  five := P.five
  five_join := ⟨(MulEquiv.subgroupCongr P.five_join).trans O.equiv⟩
  five_fixer := ⟨O.fiveFixerEquiv P⟩

end ComponentCoordinates
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.Representatives.FiveLocal
