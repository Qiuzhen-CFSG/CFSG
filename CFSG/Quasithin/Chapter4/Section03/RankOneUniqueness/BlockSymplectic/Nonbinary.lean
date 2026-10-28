module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockSymplectic.Parabolic
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SymplecticNonbinary

/-!
# The original symplectic parabolic over a nonbinary field

The original L-image is a parabolic residual. Its action on the nonzero full
module W excludes the point residual, leaving the plane residual in the same
natural coordinates. This gives the literal quotient on L O₂(K), including
its kernel and its restriction to L, without assuming the field has order four.
The existing field-four marking remains unchanged.

Source: Aschbacher--Smith C.4.5 and 4.3.7, pp.152,615--616.
-/
@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonbinarySymplectic
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
/-- An actual parabolic marking, not an assumed nonsplitting conclusion.
The quotient formula fixes the original embedding of L and O₂(K). -/
structure BlockSymplecticParabolic (c : SourceConfiguration T L) where
  F : Type
  field : Field F
  finite : Finite F
  charTwo : CharP F 2
  degree : ℕ
  large : 1 < degree
  card : Nat.card F = 2 ^ degree
  rho : Sp F →* MulAut (Multiplicative ((Fin 2 ⊕ Fin 2) → F))
  model : ChapterC.BlockModuleModel c.K rho
  linear : ∀ (g : Sp F) (v : Multiplicative ((Fin 2 ⊕ Fin 2) → F)),
    (rho g v).toAdd = Matrix.mulVec g.val v.toAdd
  quotient : c.blockLocal →* planeLocal (F := F)
  quotient_compatibility : ∀ (x : c.blockLocal) (k : c.K),
    (k.val.val : G) = x.val →
      (quotient x).val = model.quotientIso (QuotientGroup.mk' (pCore 2 c.K) k)
  local_surjective : Function.Surjective (quotient.comp (inclusion le_sup_left : L →* c.blockLocal))

attribute [instance] BlockSymplecticParabolic.field BlockSymplecticParabolic.finite
  BlockSymplecticParabolic.charTwo

namespace BlockSymplecticParabolic
variable {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)

abbrev localMap : L →* planeLocal (F := m.F) :=
  m.quotient.comp (inclusion le_sup_left)

omit [Finite G] in
/-- The displayed map kills exactly the original embedded two-core of K. -/
theorem quotient_ker : m.quotient.ker = c.blockCore.subgroupOf c.blockLocal := by
  ext x
  obtain ⟨k,hk,hx⟩ := c.blockLocal_le_component x.property
  let kK : c.K := ⟨k,hk⟩
  have he : kK.val.val = x.val := hx
  have hq := m.quotient_compatibility x kK he
  simp only [QuotientGroup.mk'_apply] at hq
  constructor
  · intro hz
    have hk0 : kK ∈ pCore 2 c.K := by
      apply (QuotientGroup.eq_one_iff kK).mp
      apply m.model.quotientIso.injective
      rw [map_one, ← hq]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
    change x.val ∈ c.blockCore
    rw [← he]
    exact mem_map_of_mem c.H.subtype (mem_map_of_mem c.K.subtype hk0)
  · intro hx0
    obtain ⟨a,⟨b,hb,rfl⟩,ha⟩ := hx0
    have hbK : b = kK := Subtype.ext (Subtype.ext (ha.trans he.symm))
    have hk0 : kK ∈ pCore 2 c.K := hbK ▸ hb
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    rw [hq, (QuotientGroup.eq_one_iff kK).mpr hk0, map_one]
    rfl

omit [Finite G] in
/-- The original L alone covers the complete parabolic residual. -/
theorem quotient_surjective : Function.Surjective m.quotient := by
  intro x
  obtain ⟨l,hl⟩ := m.local_surjective x
  exact ⟨inclusion le_sup_left l,hl⟩

omit [Finite G] in
/-- The local kernel remains a two-group, since it lies in the original O₂(K). -/
theorem local_kernel_two : IsPGroup 2 m.localMap.ker := by
  have hQ : IsPGroup 2 c.blockCore :=
    (pCore_isPGroup.map c.K.subtype).map c.H.subtype
  have hk : m.localMap.ker = c.blockCore.comap L.subtype := by
    ext l
    change m.quotient (inclusion le_sup_left l) = 1 ↔ l.val ∈ c.blockCore
    rw [← MonoidHom.mem_ker, m.quotient_ker]
    rfl
  rw [hk]
  exact hQ.comap_subtype

/-- The actual O₂(L)O₂(K)/O₂(K) section is the nonsplit plane radical.
This is an image equality under the original quotient map. -/
theorem local_core_image : (pCore 2 L).map m.localMap = Plane.radical := by
  rw [← m.localMap.comap_pCore_of_ker_isPGroup m.local_surjective m.local_kernel_two,
    map_comap_eq_self_of_surjective m.local_surjective]
  exact planeLocal_core_eq m.card m.large

/-- The complete product section, including O₂(K), has exactly that image. -/
theorem original_section_image :
    ((L.pCoreIn 2 ⊔ c.blockCore).subgroupOf c.blockLocal).map m.quotient =
      Plane.radical := by
  have hL : L.pCoreIn 2 ≤ c.blockLocal := (pCoreIn_le 2 L).trans le_sup_left
  have hm : (pCore 2 L).map (inclusion le_sup_left : L →* c.blockLocal) =
      (L.pCoreIn 2).subgroupOf c.blockLocal := by
    apply map_injective c.blockLocal.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le hL]
    rfl
  have hz : m.quotient.ker.map m.quotient = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr le_rfl
  rw [subgroupOf_sup hL le_sup_right, Subgroup.map_sup, ← hm, map_map,
    ← m.quotient_ker, hz, sup_bot_eq]
  exact m.local_core_image

end BlockSymplecticParabolic

namespace BlockSymplecticParabolic
variable {V : Subgroup G} (D : Chapter12.Section02.ChosenModule T L V)
  {c : SourceConfiguration T L} (m : BlockSymplecticParabolic c)

include D in
/-- The crossed two-group has normal image under the original L-action,
so its image lies in the actual parabolic radical. -/
theorem crossed_image_le_radical (hcross : c.crossedBlockLayer ≤ c.blockLocal) :
    (m.quotient.comp (inclusion hcross)).range ≤ Plane.radical := by
  let r := m.quotient.comp (inclusion hcross)
  have hr (l : L) (u : c.crossedBlockLayer) :
      r (blockConjugateBy L c.crossedBlockLayer (c.crossedBlockLayer_normalized D) l u) =
        m.localMap l * r u * (m.localMap l)⁻¹ := by
    change m.quotient ⟨l.val * u.val * l.val⁻¹, _⟩ = _
    have he : (⟨l.val * u.val * l.val⁻¹, _⟩ : c.blockLocal) =
        inclusion le_sup_left l * inclusion hcross u * (inclusion le_sup_left l)⁻¹ := rfl
    rw [he, map_mul, map_mul, map_inv]
    rfl
  have hn : r.range.Normal := ⟨by
    rintro x ⟨u,rfl⟩ g
    obtain ⟨l,rfl⟩ := m.local_surjective g
    exact ⟨_,hr l u⟩⟩
  have hp : IsPGroup 2 r.range :=
    (T.isPGroup'.to_le (c.crossedBlockLayer_le_sylow.trans inf_le_left)).of_surjective
      r.rangeRestrict r.rangeRestrict_surjective
  have hle : r.range ≤ pCore 2 (planeLocal (F := m.F)) := le_sSup ⟨hn,hp⟩
  exact hle.trans_eq
    (planeLocal_core_eq m.card m.large)

end BlockSymplecticParabolic

/-- The original full module rules out the point residual in the given natural marking. -/
theorem block_symplectic_not_point
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
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
  apply ChapterC.SymplecticNonbinary.symplectic_not_point_of_moved_core_fixed hF hn m hrho A B hBU hBne hBA hfix
  simpa only [SourceConfiguration.componentQuotientL,A,f,subgroupOf,comap_comap,←map_map] using he

/-- Construct the literal local quotient from a plane marking of the original L. -/
noncomputable def BlockSymplecticParabolic.of_plane_image
    (c : SourceConfiguration T L)
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
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
    degree := n
    large := hn
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


/-- The actual natural model determines the plane marking over its own field. -/
theorem parabolic_of_natural
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (F : ChapterB.QuasisimpleSource.BinaryField) (hF : 1 < F.degree)
    (hm : IsLinearBlockModel c.K (ChapterB.QuasisimpleSource.binarySymplectic F)) :
    Nonempty (BlockSymplecticParabolic c) := by
  obtain ⟨rho,⟨m⟩,hrho⟩ := hm
  obtain ⟨g,hg⟩ := c.block_symplectic_local_conjugate hF hf hb F.card_eq m.quotientIso
  let m' := m.innerMarking g
  have he : c.componentQuotientL.map m'.quotientIso.toMonoidHom = planeLocal :=
    hg.resolve_left (block_symplectic_not_point c hf F.card_eq hF m' hrho)
  exact ⟨BlockSymplecticParabolic.of_plane_image c F.card_eq hF m' hrho he⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonbinarySymplectic
