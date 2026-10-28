module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Preparation
public import CFSG.Quasithin.Chapter12.Section05.ExteriorGeometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# Exterior A₃ geometry on the original ambient actor

The literal LT actor transports exterior fixed spaces and commutator spaces
back into V. Every subgroup of its image has an ambient lift with the same
relative index. Applying E.3.7 to these lifts proves the exterior small-index
fixed-space condition for a conjugate A=Vᵍ inside T when s(G,V)=3.

The intrinsic exterior calculation then gives [V,A]=V₆. Its fixed spaces
for subgroups of quotient rank at most three generate V; if r(G,V)>3,
each such fixed subgroup normalizes A. This establishes the reverse
normalization needed for symmetry, with no assumption on the weak closure.
The numerical premises are the independent source result 12.5.6.

Source: Aschbacher--Smith, 12.5.7, printed p.820, using E.3.7, E.3.10 and
E.3.32. The underlying exterior calculation is in Section05.ExteriorGeometry.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)

/-- Exterior coordinates distinguish ambient subspaces. -/
theorem subspace_injective : Function.Injective a.subspace := by
  intro X Y he
  ext w
  let v := a.coordinates.symm (Multiplicative.ofAdd w)
  have hh := congrArg (fun C : Subgroup G => (v : G) ∈ C) he
  simpa only [a.mem_subspace, v, MulEquiv.apply_symm_apply, toAdd_ofAdd] using iff_of_eq hh

/-- The full coordinate space is the original subgroup V. -/
theorem subspace_top : a.subspace ⊤ = V := by
  apply le_antisymm (a.subspace_le _)
  intro v hv
  exact (a.mem_subspace ⊤ ⟨v, hv⟩).mpr trivial

/-- Coordinate transport preserves arbitrary generated subspaces. -/
theorem subspace_iSup {ι : Sort*}
    (W : ι → Submodule (ZMod 2) SL5ExteriorSquare.V) :
    a.subspace (⨆ i, W i) = ⨆ i, a.subspace (W i) := by
  have he (X : Submodule (ZMod 2) SL5ExteriorSquare.V) :
      a.subspace X = ((AddSubgroup.toSubgroup X.toAddSubgroup).map
        a.coordinates.symm.toMonoidHom).map V.subtype := by
    unfold subspace
    congr 1
    exact (map_eq_comap_of_inverse (f := a.coordinates.symm.toMonoidHom)
      (g := a.coordinates.toMonoidHom) a.coordinates.apply_symm_apply
      a.coordinates.symm_apply_apply _).symm
  simp only [he]
  have ha : (⨆ i, W i).toAddSubgroup = ⨆ i, (W i).toAddSubgroup :=
    (AddSubgroup.toZModSubmodule 2).symm.map_iSup W
  rw [ha, AddSubgroup.toSubgroup.map_iSup, Subgroup.map_iSup, Subgroup.map_iSup]

end ExteriorMarking
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The image of an ambient subgroup under the literal LT actor. -/
def actorImage (A : Subgroup G) : Subgroup SL5TenDimensional.Group :=
  (A.subgroupOf (L ⊔ (T : Subgroup G))).map s.actor

/-- A subgroup of the original T acts through the chosen standard flag. -/
theorem actorImage_le_flag {A : Subgroup G} (hA : A ≤ (T : Subgroup G)) :
    s.actorImage A ≤ SL5ExteriorSquare.flagGroup := by
  rintro _ ⟨a, ha, rfl⟩
  exact s.sylow_flag ⟨a, hA ha⟩

/-- Lift an image subgroup through the literal actor with unchanged quotient corank. -/
theorem lift_actorImage {A : Subgroup G} (hA : A ≤ L ⊔ (T : Subgroup G))
    (B : Subgroup SL5TenDimensional.Group) (hB : B ≤ s.actorImage A) :
    ∃ C ≤ A, s.actorImage C = B ∧
      subgroupCorank A C = Nat.log 2 (B.relIndex (s.actorImage A)) := by
  let H := L ⊔ (T : Subgroup G)
  let X := A.subgroupOf H
  let Y := X ⊓ B.comap s.actor
  let C := Y.map H.subtype
  have hCA : C ≤ A := by rintro _ ⟨x, hx, rfl⟩; exact hx.1
  have hCH : C.subgroupOf H = Y := comap_map_eq_self_of_injective H.subtype_injective Y
  have himg : Y.map s.actor = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx.2
    · intro b hb
      obtain ⟨x, hx, he⟩ := hB hb
      exact ⟨x, ⟨hx, (show s.actor x ∈ B from he.symm ▸ hb)⟩, he⟩
  refine ⟨C, hCA, ?_, ?_⟩
  · change (C.subgroupOf H).map s.actor = B
    rw [hCH, himg]
  · unfold subgroupCorank
    congr 1
    rw [← relIndex_subgroupOf (H := C) hA, hCH]
    exact (inf_relIndex_left X (B.comap s.actor)).trans (relIndex_comap B s.actor X)

/-- Model fixed vectors are the literal ambient relative centralizer. -/
theorem subspace_fixedSpace {A : Subgroup G} (hA : A ≤ L ⊔ (T : Subgroup G)) :
    s.marking.subspace (BinaryOffender.fixedSpace (SL5TenDimensional.exteriorAction 2)
      (s.actorImage A)) = V ⊓ centralizer (A : Set G) := by
  ext v
  constructor
  · intro hv
    have hvV := s.marking.subspace_le _ hv
    have hw := (s.marking.mem_subspace _ ⟨v, hvV⟩).mp hv
    refine ⟨hvV, ?_⟩
    intro a ha
    let aH : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨a, hA ha⟩
    have hf := hw ⟨s.actor aH, ⟨aH, ha, rfl⟩⟩
    change SL5TenDimensional.exteriorAction 2 (s.actor aH)
      (s.marking.coordinates ⟨v, hvV⟩).toAdd = (s.marking.coordinates ⟨v, hvV⟩).toAdd at hf
    have he := s.equivariant aH ⟨v, hvV⟩
    rw [hf] at he
    have hc := congrArg (fun w : V => (w : G)) (s.marking.coordinates.injective he)
    exact mul_inv_eq_iff_eq_mul.mp hc
  · rintro ⟨hvV, hc⟩
    apply (s.marking.mem_subspace _ ⟨v, hvV⟩).mpr
    rintro ⟨a, ha⟩
    obtain ⟨aH, haH, rfl⟩ := ha
    have he := s.equivariant aH ⟨v, hvV⟩
    have hf : (⟨(aH : G) * v * (aH : G)⁻¹,
        (mem_normalizer_iff.mp (s.normalizes aH.property) v).mp hvV⟩ : V) = ⟨v, hvV⟩ := by
      apply Subtype.ext
      change (aH : G) * v * (aH : G)⁻¹ = v
      rw [hc aH haH, mul_inv_cancel_right]
    rw [hf] at he
    exact (congrArg Multiplicative.toAdd he).symm

variable [Finite G]

/-- E.3.7 supplies the A₃ fixed-space condition in the actual exterior image. -/
theorem actorImage_smallIndex_three (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hs : let := D.elementary; globalS V = 3) :
    SL5ExteriorSquare.HasSmallIndexFixedSpaceProperty 3
      (s.actorImage (V.map (MulAut.conj g).toMonoidHom)) := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  have hAH : A ≤ L ⊔ (T : Subgroup G) := hg.trans le_sup_right
  intro B hB hsmall
  obtain ⟨C, hCA, hCB, hcor⟩ := s.lift_actorImage hAH B hB
  apply s.marking.subspace_injective
  rw [← hCB, s.subspace_fixedSpace hAH, s.subspace_fixedSpace (hCA.trans hAH)]
  symm
  apply lemma_E_3_7 g (le_inf hCA ((hCA.trans hAH).trans s.normalizes))
  rw [hs, hcor]
  exact_mod_cast hsmall

omit [Finite G] in
/-- Action differences transport to the actual ambient commutator subgroup. -/
theorem subspace_commutator {A : Subgroup G} (hA : A ≤ L ⊔ (T : Subgroup G)) :
    s.marking.subspace (BinaryOffender.subspaceCommutator
      (SL5TenDimensional.exteriorAction 2) ⊤ (s.actorImage A)) = ⁅V, A⁆ := by
  let : Module (ZMod 2) (Additive (Multiplicative SL5ExteriorSquare.V)) :=
    inferInstanceAs (Module (ZMod 2) SL5ExteriorSquare.V)
  let ρ : Representation (ZMod 2) SL5TenDimensional.Group
      (Additive (Multiplicative SL5ExteriorSquare.V)) := SL5TenDimensional.exteriorAction 2
  let f : A →* SL5TenDimensional.Group := s.actor.comp (inclusion hA)
  have hf : f.range = s.actorImage A := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨inclusion hA a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have he := BinaryOffender.commutator_image_eq ρ V V A (hA.trans s.normalizes)
    le_rfl f s.marking.coordinates.toMonoidHom (fun a v => by
      exact (congrArg Multiplicative.toAdd (s.equivariant (inclusion hA a) v)).symm)
    ⊤ (by
      rw [subgroupOf_self, map_top_of_surjective _ s.marking.coordinates.surjective]
      rfl)
  rw [hf] at he
  have hc : ⁅V, A⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hA.trans s.normalizes)
  change ((BinaryOffender.binarySubgroup
    (BinaryOffender.subspaceCommutator ρ ⊤ (s.actorImage A))).comap
      s.marking.coordinates.toMonoidHom).map V.subtype = _
  rw [← he, comap_map_eq_self_of_injective s.marking.coordinates.injective,
    map_subgroupOf_eq_of_le hc]

/-- The A₃ calculation and r>3 give the commutator and reverse normalization. -/
theorem conjugate_three_geometry (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hnon : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hs : let := D.elementary; globalS V = 3)
    (hr : (3 : ℕ∞) < globalR V) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = s.marking.Vi 6 ∧
      V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ L ⊔ (T : Subgroup G) := hg.trans le_sup_right
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hAH
  let _ : IsElementaryAbelian 2 (s.actorImage A) := IsElementaryAbelian.map _
  have hne : s.actorImage A ≠ ⊥ := by
    intro he
    have hc := s.subspace_fixedSpace hAH
    rw [he, BinaryOffender.fixedSpace_bot, s.marking.subspace_top] at hc
    exact hnon (commutator_eq_bot_iff_le_centralizer.mpr (inf_eq_left.mp hc.symm))
  obtain ⟨_, _, hcomm, hspan⟩ := ExteriorGeometry.smallIndex_three_module_geometry
    (s.actorImage A) (s.actorImage_le_flag hg) hne (s.actorImage_smallIndex_three g hg hs)
  constructor
  · rw [← s.subspace_commutator hAH, hcomm]
    rfl
  · change V ≤ normalizer (A : Set G)
    conv_lhs => rw [← s.marking.subspace_top, ← hspan, s.marking.subspace_iSup]
    apply iSup_le
    intro B
    rw [s.marking.subspace_iSup]
    apply iSup_le
    intro hB
    rw [s.marking.subspace_iSup]
    apply iSup_le
    intro hb
    obtain ⟨C, hCA, he, hcor⟩ := s.lift_actorImage hAH B hB
    rw [← he, s.subspace_fixedSpace (hCA.trans hAH)]
    apply inf_le_right.trans
    apply centralizer_le_normalizer_of_corank_lt_globalR hCA
    rw [globalR_map_equiv, hcor]
    exact lt_of_le_of_lt (by exact_mod_cast hb) hr

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
