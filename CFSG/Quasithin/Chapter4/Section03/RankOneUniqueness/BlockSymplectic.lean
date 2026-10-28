module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockCrossing
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.GroupTheory.PCoreSurjective

/-!+# The original section in the symplectic block branch

The block core is embedded through K ≤ H ≤ G, and the local group is the
literal join L O₂(K). A parabolic marking identifies the original quotient
map and the actual natural action, and requires the image of the original L
to be the plane local. Constructing this marking is a C.4.1 obligation.

The crossed layer remains in S = T ∩ H and escapes the embedded O₂(K),
by the common crossing argument. The full module is always
[Ω₁Z(O₂(LT)),L].

The terminal implication uses the proved matrix nonsplitting theorem:
normality puts the crossed image in the plane radical, and its natural
quotient forces that image to vanish. The parabolic marking and the module
geometry are explicit independent obligations. Their existence is not
asserted here, so this module does not yet prove the source Sp₄(4) branch.

Source: Aschbacher--Smith, C.4.1(2), I.2.3(3) and 4.3.7,
refs/quasithin.pdf, printed pp.151,413 and616.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

abbrev SourceConfiguration.blockCore (c : SourceConfiguration T L) : Subgroup G :=
  ((pCore 2 c.K).map c.K.subtype).map c.H.subtype

abbrev SourceConfiguration.blockLocal (c : SourceConfiguration T L) : Subgroup G :=
  L ⊔ c.blockCore

abbrev SourceConfiguration.crossedBlockLayer (c : SourceConfiguration T L) : Subgroup G :=
  c.blockLayer.map (MulAut.conj c.t⁻¹).toMonoidHom

abbrev SourceConfiguration.blockFullModule (_c : SourceConfiguration T L) : Subgroup G :=
  Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)

omit [Finite G] in
theorem SourceConfiguration.blockLayer_le_blockCore (c : SourceConfiguration T L) :
    c.blockLayer ≤ c.blockCore := map_mono (map_mono ChapterC.blockU_le_core)

omit [Finite G] in
theorem SourceConfiguration.blockCore_le_component (c : SourceConfiguration T L) :
    c.blockCore ≤ c.K.map c.H.subtype := map_mono (map_subtype_le _)

omit [Finite G] in
theorem SourceConfiguration.blockLocal_le_component (c : SourceConfiguration T L) :
    c.blockLocal ≤ c.K.map c.H.subtype :=
  sup_le c.le_component c.blockCore_le_component

omit [Finite G] in
theorem SourceConfiguration.blockCore_le_joinCore (c : SourceConfiguration T L) :
    c.blockCore ≤
      (c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)).pCoreIn 2 := by
  let J := c.K.map c.H.subtype ⊔ ((T : Subgroup G) ⊓ c.H)
  have hn : J ≤ normalizer (c.blockCore : Set G) :=
    (sup_le (map_subtype_le _) inf_le_right).trans
      (c.normalizer_component.le.trans
        (normalizer_le_normalizer_characteristic_map c.H.subtype c.H.subtype_injective
          c.K (pCore 2 c.K)))
  exact le_pCoreIn_of_normalizes ((pCore_isPGroup.map c.K.subtype).map c.H.subtype)
    (c.blockCore_le_component.trans le_sup_left) hn

theorem SourceConfiguration.crossedBlockLayer_not_le_blockCore
    (c : SourceConfiguration T L) (hb : ChapterC.IsBlock c.K) :
    ¬ c.crossedBlockLayer ≤ c.blockCore :=
  fun hh => c.block_crossing_not_le_core hb (hh.trans c.blockCore_le_joinCore)

theorem SourceConfiguration.crossedBlockLayer_le_sylow (c : SourceConfiguration T L) :
    c.crossedBlockLayer ≤ (T : Subgroup G) ⊓ c.H := by
  have hs : (((T : Subgroup G) ⊓ c.H).map (MulAut.conj c.t⁻¹).toMonoidHom) =
      (T : Subgroup G) ⊓ c.H := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (((T : Subgroup G) ⊓ c.H) : Set G)).inv_mem c.crossing_normalizes)
  exact (map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom)
    c.blockLayer_le_sylow).trans_eq hs

omit [Finite G] in
theorem SourceConfiguration.crossedBlockLayer_normalized {V : Subgroup G}
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V) :
    L ≤ normalizer (c.crossedBlockLayer : Set G) := by
  have hL : L.map (MulAut.conj c.t⁻¹).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp
      (D.sylow_normalizes_component ((T : Subgroup G).inv_mem c.crossing_mem))
  have hn := (map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom)
    ((c.le_I.trans c.I_le_H).trans c.blockLayer_normalized)).trans
      (c.blockLayer.le_normalizer_map (MulAut.conj c.t⁻¹).toMonoidHom)
  simpa only [hL] using hn

omit [Finite G] in
/-- Crossing preserves the literal full module, placing it in both copies. -/
theorem SourceConfiguration.blockFullModule_le_crossed {V : Subgroup G}
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hfull : c.blockFullModule ≤ c.blockLayer) :
    c.blockFullModule ≤ c.blockLayer ⊓ c.crossedBlockLayer := by
  refine le_inf hfull ?_
  have hm := map_mono (f := (MulAut.conj c.t⁻¹).toMonoidHom) hfull
  change c.blockFullModule.map (MulAut.conj c.t⁻¹).toMonoidHom ≤ c.crossedBlockLayer at hm
  rw [show c.blockFullModule.map (MulAut.conj c.t⁻¹).toMonoidHom = c.blockFullModule from
    c.crossing_fullModule D] at hm
  exact hm

/-- An actual parabolic marking, not an assumed nonsplitting conclusion.
The quotient formula fixes the original embedding of L and O₂(K). -/
structure BlockSymplecticParabolic (c : SourceConfiguration T L) where
  F : Type
  field : Field F
  finite : Finite F
  charTwo : CharP F 2
  card : Nat.card F = 4
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
  exact planeLocal_core_eq (by simpa using m.card : Nat.card m.F = 2 ^ 2) (by decide)

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

omit [Finite G] in
/-- A literal conjugate in a normalized subgroup. -/
def blockConjugateBy (A B : Subgroup G) (hn : A ≤ normalizer (B : Set G))
    (a : A) (b : B) : B :=
  ⟨a.val * b.val * a.val⁻¹, (mem_normalizer_iff.mp (hn a.property) b.val).mp b.property⟩

/-- The module-geometry obligations of 4.3.7, on the original two copies.
The natural maps have exactly the literal full module as kernel. -/
structure BlockSymplecticGeometry {V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (c : SourceConfiguration T L)
    (m : BlockSymplecticParabolic c) where
  full_le : c.blockFullModule ≤ c.blockLayer
  fixed_le : c.blockLayer ⊓ centralizer (c.K.map c.H.subtype : Set G) ≤ c.blockFullModule
  crossed_le : c.crossedBlockLayer ≤ c.blockLocal
  natural : c.blockLayer →* Multiplicative (Fin 2 → m.F)
  natural_surjective : Function.Surjective natural
  natural_kernel : natural.ker = c.blockFullModule.subgroupOf c.blockLayer
  natural_action : ∀ (l : L) (u : c.blockLayer),
    natural (blockConjugateBy L c.blockLayer
      ((c.le_I.trans c.I_le_H).trans c.blockLayer_normalized) l u) =
      Multiplicative.ofAdd (Matrix.mulVec (Plane.quotientMap (m.localMap l)).val
        (natural u).toAdd)
  crossed : c.crossedBlockLayer →* Multiplicative (Fin 2 → m.F)
  crossed_surjective : Function.Surjective crossed
  crossed_kernel : crossed.ker = c.blockFullModule.subgroupOf c.crossedBlockLayer
  crossed_action : ∀ (l : L) (u : c.crossedBlockLayer),
    crossed (blockConjugateBy L c.crossedBlockLayer (c.crossedBlockLayer_normalized D) l u) =
      Multiplicative.ofAdd (Matrix.mulVec (Plane.quotientMap (m.localMap l)).val
        (crossed u).toAdd)

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
    (planeLocal_core_eq (by simpa using m.card : Nat.card m.F = 2 ^ 2) (by decide))

end BlockSymplecticParabolic

/-- Conditional terminal application of the nonsplit obstruction. The original
source hypotheses must still construct both the parabolic marking and the
two natural quotient maps; this theorem does not assert their existence. -/
theorem SourceConfiguration.false_of_symplectic_geometry {V : Subgroup G}
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hb : ChapterC.IsBlock c.K) (m : BlockSymplecticParabolic c)
    (d : BlockSymplecticGeometry D c m) : False := by
  let r := m.quotient.comp (inclusion d.crossed_le)
  have hk : d.crossed.ker ≤ r.ker := by
    intro u hu
    have hw : u.val ∈ c.blockFullModule := by
      simpa only [d.crossed_kernel, mem_subgroupOf] using hu
    have hc : u.val ∈ c.blockCore := c.blockLayer_le_blockCore (d.full_le hw)
    change inclusion d.crossed_le u ∈ m.quotient.ker
    rw [m.quotient_ker]
    exact hc
  let f := d.crossed.liftOfSurjective d.crossed_surjective ⟨r,hk⟩
  have hf (u : c.crossedBlockLayer) : f (d.crossed u) = r u := by simp [f]
  have hR : f.range ≤ Plane.radical := by
    rintro x ⟨v,rfl⟩
    obtain ⟨u,rfl⟩ := d.crossed_surjective v
    rw [hf]
    exact m.crossed_image_le_radical D d.crossed_le ⟨u,rfl⟩
  have he (g : planeLocal (F := m.F)) (v : Multiplicative (Fin 2 → m.F)) :
      f (Multiplicative.ofAdd (Matrix.mulVec (Plane.quotientMap g).val v.toAdd)) =
        g * f v * g⁻¹ := by
    obtain ⟨l,rfl⟩ := m.local_surjective g
    obtain ⟨u,rfl⟩ := d.crossed_surjective v
    rw [← d.crossed_action, hf, hf]
    change m.quotient ⟨l.val * u.val * l.val⁻¹, _⟩ = _
    have hh : (⟨l.val * u.val * l.val⁻¹, _⟩ : c.blockLocal) =
        inclusion le_sup_left l * inclusion d.crossed_le u * (inclusion le_sup_left l)⁻¹ := rfl
    rw [hh, map_mul, map_mul, map_inv]
    rfl
  have hz := Plane.natural_hom_into_radical_eq_one
    (by simpa using m.card : Nat.card m.F = 2 ^ 2) (by decide) f hR he
  apply c.crossedBlockLayer_not_le_blockCore hb
  intro u hu
  have hr : r ⟨u,hu⟩ = 1 := by rw [← hf ⟨u,hu⟩,hz]; rfl
  have hh : inclusion d.crossed_le ⟨u,hu⟩ ∈ m.quotient.ker := hr
  rw [m.quotient_ker] at hh
  exact hh

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
