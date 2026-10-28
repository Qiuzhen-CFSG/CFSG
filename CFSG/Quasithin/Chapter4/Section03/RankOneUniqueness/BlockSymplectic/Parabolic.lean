module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.Recognition
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockModuleContainment
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SymplecticPointExclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.InnerMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic

/-!
# The original plane-parabolic marking in the Sp₄(4) block branch

The actual full module is nonzero, fully moved by L and centralized by O₂(L).
The point-radical calculation therefore excludes the point residual in the
simultaneous local recognition. Inner conjugation transports both the original
quotient and its given natural module to the remaining plane marking.

The resulting quotient on the literal L O₂(K) agrees with K → K/O₂(K) under
both original inclusions, and L itself maps onto the plane residual. This
constructs BlockSymplecticParabolic, discharging the parabolic-marking input
of BlockSymplectic.false_of_symplectic_geometry. The crossed natural-module
geometry and C.4.1 block classification remain with the final assembly owner,
qt-d-1222-rankone-uniqueness-block; no such geometry is assumed or asserted here.
The full module is never identified with the separately chosen Chapter12 module.

Source: Aschbacher–Smith C.4.1(2) and original 4.3.7, printed pp.151–153,616.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original full module rules out the point residual in the given natural marking. -/
theorem SourceConfiguration.block_symplectic_not_point
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel c.K rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd) :
    c.componentQuotientL.map m.quotientIso.toMonoidHom ≠ pointLocal := by
  intro he
  let W := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hfr : f.range = c.K.map c.H.subtype := by
    rw [MonoidHom.range_comp, range_subtype]
  have hU : (blockU c.K).map f = c.blockLayer := by rw [← map_map]
  let A := L.comap f
  let B := W.comap f
  have hLA : A.map f = L := map_comap_eq_self (by rw [hfr]; exact c.le_component)
  have hWL : W ≤ L := by
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    simpa only [hs] using c.c28.module_le
  have hWB : B.map f = W := map_comap_eq_self (hWL.trans (by rw [hfr]; exact c.le_component))
  have hBU : B ≤ blockU c.K := by
    intro b hb
    apply (mem_map_iff_mem hfi).mp
    rw [hU]
    exact c.fullModule_le_blockLayer hf hb
  have hBne : B ≠ ⊥ := by
    intro he
    have hWne := c.c28.module_nontrivial
    apply hWne
    change W = ⊥
    rw [← hWB, he, Subgroup.map_bot]
  have hBA : ⁅B,A⁆ = B := by
    apply map_injective hfi
    rw [map_commutator, hWB, hLA]
    have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
      le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
    exact (show W = ⁅W,L⁆ from by simpa only [hs] using c.c28.module_commutator).symm
  have hIN : c.I ≤ normalizer (L : Set G) := by
    rw [c.I_eq]
    exact sup_le L.le_normalizer (c.c28.radical_le.trans inf_le_right)
  have hcore : L.pCoreIn 2 ≤ c.I.pCoreIn 2 := pCoreIn_mono_of_normalizes c.le_I hIN
  have hfix : B ≤ centralizer (A.pCoreIn 2 : Set c.K) := by
    intro w hw a ha
    apply hfi
    change f a * f w = f w * f a
    have haL : f a ∈ L.pCoreIn 2 := by
      have hm := mem_map_of_mem f ha
      rwa [map_pCoreIn_of_injective 2 A f hfi,hLA] at hm
    obtain ⟨v,hv,hvw⟩ := c.c28.module_le_center_radical hw
    have hc := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
      (mem_center_iff.mp hv ⟨f a,hcore haL⟩)
    change f a * (v : G) = (v : G) * f a at hc
    change (v : G) = f w at hvw
    rwa [hvw] at hc
  apply m.symplectic_not_point_of_moved_core_fixed hF hrho A B hBU hBne hBA hfix
  simpa only [SourceConfiguration.componentQuotientL,A,f,subgroupOf,comap_comap,←map_map] using he

/-- Construct the literal local quotient from a plane marking of the original L. -/
noncomputable def BlockSymplecticParabolic.of_plane_image
    (c : SourceConfiguration T L)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {rho : Sp F →* MulAut (Multiplicative (Vector F))}
    (m : BlockModuleModel c.K rho)
    (hrho : ∀ g v, (rho g v).toAdd = g.val.mulVec v.toAdd)
    (he : c.componentQuotientL.map m.quotientIso.toMonoidHom = planeLocal) :
    BlockSymplecticParabolic c := by
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  let p := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.K))
  let eK : c.K ≃* c.K.map c.H.subtype := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  let j : c.blockLocal →* c.K := eK.symm.toMonoidHom.comp (inclusion c.blockLocal_le_component)
  have hj (x : c.blockLocal) : f (j x) = x.val := by
    exact congrArg (fun y : c.K.map c.H.subtype => (y : G))
      (eK.apply_symm_apply (inclusion c.blockLocal_le_component x))
  have hlocal : c.blockLocal ≤ (planeLocal.comap p).map f := by
    apply sup_le
    · intro l hl
      obtain ⟨k,hk,hkl⟩ := c.le_component hl
      let a : c.K := ⟨k,hk⟩
      refine ⟨a,?_,hkl⟩
      change p a ∈ planeLocal
      rw [←he]
      refine ⟨QuotientGroup.mk' (pCore 2 c.K) a,⟨a,?_,rfl⟩,rfl⟩
      change (k : G) ∈ L
      change (k : G) = l at hkl
      rwa [hkl]
    · rintro x ⟨k,⟨a,ha,rfl⟩,rfl⟩
      refine ⟨a,?_,rfl⟩
      change m.quotientIso (QuotientGroup.mk' (pCore 2 c.K) a) ∈ planeLocal
      rw [QuotientGroup.mk'_apply,(QuotientGroup.eq_one_iff a).mpr ha,map_one]
      exact one_mem _
  have hmem (x : c.blockLocal) : p (j x) ∈ planeLocal := by
    obtain ⟨a,ha,hax⟩ := hlocal x.property
    have hx : a = j x := hfi (hax.trans (hj x).symm)
    exact hx ▸ ha
  let q : c.blockLocal →* planeLocal (F := F) := (p.comp j).codRestrict _ hmem
  refine {
    F := F
    field := inferInstance
    finite := inferInstance
    charTwo := inferInstance
    card := hF
    rho := rho
    model := m
    linear := hrho
    quotient := q
    quotient_compatibility := ?_
    local_surjective := ?_ }
  · intro x k hk
    change p (j x) = p k
    exact congrArg p (hfi ((hj x).trans hk.symm))
  · intro y
    have hy : y.val ∈ c.componentQuotientL.map m.quotientIso.toMonoidHom := he.symm ▸ y.property
    obtain ⟨z,⟨k,hk,rfl⟩,hz⟩ := hy
    let l : L := ⟨k.val.val,hk⟩
    refine ⟨l,?_⟩
    apply Subtype.ext
    change p (j (inclusion le_sup_left l)) = y.val
    have hjk : j (inclusion le_sup_left l) = k := hfi (hj _)
    rw [hjk]
    exact hz

/-- The Sp₄(4) block supplies its original plane-residual marking with no
 additional quotient-image or action-placement premise. -/
theorem SourceConfiguration.block_symplectic_parabolic
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsp : IsSp4FourBlock c.K) : Nonempty (BlockSymplecticParabolic c) := by
  obtain ⟨_,F,_,_,hF,rho,⟨m⟩,hrho⟩ := hsp
  let : Fintype F := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [←Nat.card_eq_fintype_card,hF])
  let : CharP F 2 := ringChar.of_eq hc
  obtain ⟨g,hg⟩ := c.block_symplectic_local_conjugate (n := 2) (by decide) hf hb hF m.quotientIso
  let m' := m.innerMarking g
  have he : c.componentQuotientL.map m'.quotientIso.toMonoidHom = planeLocal :=
    hg.resolve_left (c.block_symplectic_not_point hf hF m' hrho)
  exact ⟨BlockSymplecticParabolic.of_plane_image c hF m' hrho he⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
