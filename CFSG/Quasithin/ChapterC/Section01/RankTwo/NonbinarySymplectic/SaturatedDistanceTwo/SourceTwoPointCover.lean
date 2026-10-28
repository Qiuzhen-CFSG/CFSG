module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoRadicalBound
public import Theory.SpecificGroups.SymplecticFour.MaximalElementary.Point

/-!
# The full radical is a point radical on the original natural cover

In the large-movement branch the full marked image is elementary abelian
of order q³. Transport through the exact whole-core kernel gives this
property to the action on the existing ambient natural cover. A quadratic
image would have natural displacement dimension at most two and, by full
fixed-vector lifting, movement index at most q². This contradicts the
actual opposite-core movement. The maximal elementary classification then
selects the point radical by symplectic conjugation.

The resulting cover retains the original field degree, complete projection
kernel, full ambient quotient and the literal equation relating that quotient
to the entire common-radical actor. No separate natural-action witness or
coordinate compatibility assumption is added.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.7)(2), printed p.873. The subsequent fixed-core index squeeze remains.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour

private theorem cover_moving_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    (centralizer (A : Set G)).relIndex U =
      Nat.card F ^ Module.finrank F
        (displacementSpace ((commutator (Sp F)).subtype.comp β).range) := by
  let α := (commutator (Sp F)).subtype.comp β
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  rw [hi]
  change 2 ^ Module.finrank (ZMod 2)
    (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
  rw [hfixed]
  have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (TwoLocalCover.fixedSpace α.range)).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  rw [hc,fixed_quotient_card]


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource

section Covers
variable {M J W : Type*} [Group M] [Group J] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : Representation (ZMod 2) J W} {C : Subgroup J}

/-- The original ambient cover with the full common radical identified as a point radical. -/
structure RadicalPointCover (T : Subgroup M) (s : MovedSection ρ C) (n : ℕ)
    (z t : Vertex T) extends AmbientVertexCover T s n z where
  edge_le : Q T t ≤ stabilizer T z
  actor : Q T t →* L (K := field.Carrier)
  actor_marking : ∀ u : Q T t, (equiv.groupEquiv.symm (actor u) : J) =
    quotient (inclusion edge_le u)
  actor_conjugation : ∀ u : Q T t, ∀ w : s.space.toSubmodule,
    embedding (Multiplicative.ofAdd (MovedSection.coverAction s equiv (actor u) w)) =
      u.val*embedding (Multiplicative.ofAdd w)*u.val⁻¹
  actor_kernel : ((commutator (Sp field.Carrier)).subtype.comp actor).ker =
    (Q T z).subgroupOf (Q T t)
  point_image : ∃ v : Sp field.Carrier,
    ((commutator (Sp field.Carrier)).subtype.comp actor).range.map
      (MulAut.conj v).toMonoidHom = pointRadicalAmbient
end Covers

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The cubic marked radical is elementary; the full Sylow alternative is excluded. -/
theorem source_two_large_marked_radical_elementary
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    IsElementaryAbelian 2 ((d.ambient.subgroupOf K).map (componentProjection h)) := by
  rcases marked_radical_elementary_or_sylow h d g (by omega) hsat with he | ⟨S,hS⟩
  · exact he
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hc := source_two_large_marked_radical_card h d g hb hsat path hat hzt c c' hlarge
  have hsc : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = Nat.card F^4 := by
    rw [←hS]
    exact (Nat.card_congr (Sylow.equiv S
      (unipotentSylow h.field_card (by have := h.nonbinary; omega))).toEquiv).trans card_unipotent
  rw [h.field_card,hc] at hsc
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  exact False.elim ((Nat.pow_lt_pow_right hq (by decide : 3 < 4)).ne hsc)

/-- Large movement identifies the full radical on the same original natural cover. -/
theorem source_two_large_radical_point_cover
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    Nonempty (RadicalPointCover d.radical (replacementMovedSection h d) n z t) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let β := γ.comp (inclusion c'.edge_le)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hact (u : Q d.radical t) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β u) w)) =
        u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion c'.edge_le u)))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion c'.edge_le u) w
  have hαker : α.ker = (Q d.radical z).subgroupOf (Q d.radical t) := by
    have hkκ : κ.ker = (Q d.radical z).subgroupOf (stabilizer d.radical z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [α,β,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  let er := (QuotientGroup.quotientKerEquivRange α).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hαker.trans c'.action_kernel.symm)).trans
      (QuotientGroup.quotientKerEquivRange c'.action))
  let : IsElementaryAbelian 2 c'.action.range := c'.action_range.symm ▸
    source_two_large_marked_radical_elementary h d g hb hsat path hat hzt c c' hlarge
  let : IsElementaryAbelian 2 α.range :=
    IsElementaryAbelian.of_surjective er.symm.toMonoidHom er.symm.surjective
  have hc : Nat.card α.range = Nat.card E.Carrier^3 := by
    rw [←index_ker,hαker]
    change (Q d.radical z).relIndex (Q d.radical t)=_
    rw [source_two_large_full_radical_card h d g hb hsat path hat hzt c c' hlarge,
      E.card_eq,hE]
  refine ⟨{ toAmbientVertexCover := ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,
              hfaith,hsemi,hconj,hproj,hker⟩
            edge_le := c'.edge_le
            actor := β
            actor_marking := ?_
            actor_conjugation := hact
            actor_kernel := hαker
            point_image := ?_ }⟩
  · intro u
    exact congrArg Subtype.val (e.groupEquiv.symm_apply_apply (κC (inclusion c'.edge_le u)))
  · apply MaximalElementary.conjugate_point_of_not_quadratic
      (E.card_eq.trans (congrArg (2^·) hE)) (by have := h.nonbinary; omega)
      α.range hc
    intro hq
    have hdim := TwoLocalCover.finrank_le_two_of_isotropic (displacementSpace α.range)
      (quadratic_displacement_isotropic α.range hq)
    have hi := cover_moving_index (MovedSection.coverAction s e)
      (MovedSection.coverProjection s e) he (U d.radical z) (Q d.radical t)
      j hj hjr β hact
    have hsmall : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) ≤ (2^n)^2 := by
      rw [hi]
      have hh := Nat.pow_le_pow_right (show 0 < Nat.card E.Carrier from Nat.card_pos) hdim
      simpa only [E.card_eq,hE] using hh
    let := finite_Z d.radical z
    let : Finite (U d.radical z) := Finite.of_injective
      (inclusion (U_le_Z z)) (inclusion_injective _)
    have hmono := relIndex_le_of_le_left (centralizer_le c.core_le_edge)
      (show (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) ≠ 0 from index_ne_zero_of_finite)
    exact hlarge.not_ge (hmono.trans hsmall)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
