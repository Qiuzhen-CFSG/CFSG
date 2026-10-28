module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Seed
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import Theory.Representation.BinaryOffender.EquivariantOffender


/-!
# The maximum-order small-mover family in the full point core

For the actual marked binary S6 module, centralizer indices are precisely
powers of two with exponent the fixed-space codimension. Inside the marked
point core, the weak offender inequality with index at most four leaves the
trivial image, the unique transposition line, and the three mixed planes.
Maximum order therefore forces the full preimage of a mixed plane. These
preimages contain the actual two-core and generate the radical. In particular,
two subgroups moving only a line cannot generate this family.

The final application retains the original natural coordinates and projection
on the literal characteristic replacement. No elementary-abelian condition
is imposed on the family members themselves.

Source: Meierfrankenfeld--Stellmacher (1993), Sections 5.0, 5.1 and 5.4,
printed pp.912--914, in the full point-core branch. The defining inequality
is |EQ/Q| >= |W/C_W(E)| <= 4.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace SmallImages

/-- Each of the three mixed planes in the standard point core has order four. -/

theorem plane_card (i : Fin 3) : Nat.card (Model.corePlane i) = 4 := by
  rw [← Model.corePlane_conjugate]
  exact (card_map_of_injective (MulAut.conj _).injective).trans card_plus

/-- The weak source inequality in the standard point core leaves only the
trivial subgroup, the point transposition, and the three mixed planes. -/
theorem admissible_iff {A : Subgroup Model.S} (hA : A ≤ Model.E) :
    (2 ^ fixedCodim Model.rho A ≤ Nat.card A ∧
      2 ^ fixedCodim Model.rho A ≤ 4) ↔
    A = ⊥ ∨ A = last ∨ ∃ i : Fin 3, A = Model.corePlane i := by
  constructor
  · intro h
    by_cases hz : A = ⊥
    · exact Or.inl hz
    have he : IsElementaryTwo A := isElementaryTwo_exceptional.of_le hA hz
    have hc := he.card_eq_two_pow_rank
    have hd : fixedCodim Model.rho A ≤ rank A := by
      rw [hc] at h
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h.1
    have hb : IsBestOffender Model.rho A :=
      (isBestOffender_natural_iff A).mpr ((isOffender_natural_iff A).mp ⟨he,hd⟩)
    rcases (Model.best_iff hA).mp hb with hl | hp | hp | hp | hp
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr ⟨0,hp⟩)
    · exact Or.inr (Or.inr ⟨1,hp⟩)
    · exact Or.inr (Or.inr ⟨2,hp⟩)
    · subst A
      have hd := fixedCodim_exceptional.2.2.2
      change fixedCodim Model.rho Model.E = 3 at hd
      rw [hd] at h
      norm_num at h
  · rintro (rfl | rfl | ⟨i,rfl⟩)
    · have hz : fixedCodim Model.rho (⊥ : Subgroup Model.S) = 0 := by
        have hh := fixedCodim_add_finrank Model.rho (⊥ : Subgroup Model.S)
        rw [fixedSpace_bot,finrank_top] at hh
        omega
      simp [hz]
    · rw [fixedCodim_last.2.2.2,card_last]
      norm_num
    · rw [Model.corePlane_codim,plane_card]
      norm_num

private theorem map_conj_cancel (A : Subgroup Model.S) (g : Model.S) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Model.S := by ext x; simp [MulAut.conj_apply,mul_assoc]
  rw [he,map_id]

/-- A mixed plane in the inherited conjugate point marking. -/
def plane (g : Model.S) (i : Fin 3) : Subgroup Model.S :=
  (Model.corePlane i).map (MulAut.conj g).toMonoidHom

theorem plane_card_conjugate (g : Model.S) (i : Fin 3) : Nat.card (plane g i) = 4 :=
  (card_map_of_injective (MulAut.conj g).injective).trans (plane_card i)

theorem plane_codim (g : Model.S) (i : Fin 3) : fixedCodim Model.rho (plane g i) = 2 := by
  rw [plane,fixedCodim_map_conj,Model.corePlane_codim]

theorem plane_le (g : Model.S) (i : Fin 3) :
    plane g i ≤ Model.E.map (MulAut.conj g).toMonoidHom := map_mono (Model.corePlane_le i)

theorem planes_generate (g : Model.S) :
    plane g 0 ⊔ plane g 1 = Model.E.map (MulAut.conj g).toMonoidHom := by
  rw [plane,plane,← Subgroup.map_sup]
  exact congrArg (fun A : Subgroup Model.S => A.map (MulAut.conj g).toMonoidHom)
    Model.corePlanes_generate

theorem admissible_iff_conjugate (g : Model.S) {A : Subgroup Model.S}
    (hA : A ≤ Model.E.map (MulAut.conj g).toMonoidHom) :
    (2 ^ fixedCodim Model.rho A ≤ Nat.card A ∧ 2 ^ fixedCodim Model.rho A ≤ 4) ↔
    A = ⊥ ∨ A = last.map (MulAut.conj g).toMonoidHom ∨
      ∃ i : Fin 3, A = plane g i := by
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : B ≤ Model.E :=
    (map_mono hA).trans_eq (map_conj_cancel Model.E g)
  have hh := admissible_iff hB
  have hcard : Nat.card B = Nat.card A := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcodim : fixedCodim Model.rho B = fixedCodim Model.rho A := fixedCodim_map_conj _ _ _
  rw [hcard,hcodim] at hh
  rw [hh]
  constructor
  · rintro (he | he | ⟨i,he⟩)
    · exact Or.inl ((map_eq_bot_iff_of_injective A (MulAut.conj g⁻¹).injective).mp he)
    · apply Or.inr; apply Or.inl
      have h := congrArg (fun C : Subgroup Model.S => C.map (MulAut.conj g).toMonoidHom) he
      have hh := map_conj_cancel A g⁻¹
      simp only [inv_inv] at hh
      change B.map (MulAut.conj g).toMonoidHom = _ at h
      rw [hh] at h
      exact h
    · apply Or.inr; apply Or.inr; refine ⟨i,?_⟩
      have h := congrArg (fun C : Subgroup Model.S => C.map (MulAut.conj g).toMonoidHom) he
      have hh := map_conj_cancel A g⁻¹
      simp only [inv_inv] at hh
      change B.map (MulAut.conj g).toMonoidHom = plane g i at h
      rw [hh] at h
      exact h
  · rintro (rfl | rfl | ⟨i,rfl⟩)
    · exact Or.inl (map_bot _)
    · exact Or.inr (Or.inl (map_conj_cancel last g))
    · exact Or.inr (Or.inr ⟨i,map_conj_cancel (Model.corePlane i) g⟩)

end SmallImages
namespace Source
variable {M : Type*} [Group M] {L R W : Subgroup M}
  [L.Normal] [W.Normal] (s : Source L R W)

private theorem fixed_iff (E : Subgroup M) (w : W) :
    (s.coordinates w).toAdd ∈ fixedSpace Model.rho (E.map s.projection) ↔
      (w : M) ∈ centralizer (E : Set M) := by
  constructor
  · intro hw e he
    have hx := hw ⟨s.projection e,mem_map_of_mem _ he⟩
    change Model.rho (s.projection e) (s.coordinates w).toAdd = (s.coordinates w).toAdd at hx
    rw [← s.action] at hx
    have hy := s.coordinates.injective (Multiplicative.toAdd.injective hx)
    have hz : e * (w : M) * e⁻¹ = w := congrArg Subtype.val hy
    exact mul_inv_eq_iff_eq_mul.mp hz
  · intro hw a
    obtain ⟨e,he,hea⟩ := a.property
    change Model.rho (a : Model.S) (s.coordinates w).toAdd = (s.coordinates w).toAdd
    rw [← hea]
    rw [← s.action]
    congr 2
    apply Subtype.ext
    change e * (w : M) * e⁻¹ = w
    rw [hw e he,mul_inv_cancel_right]

private noncomputable def fixedEquiv (E : Subgroup M) :
    (centralizer (E : Set M)).subgroupOf W ≃ fixedSpace Model.rho (E.map s.projection) where
  toFun w := ⟨(s.coordinates w.val).toAdd,(fixed_iff s E w.val).mpr w.property⟩
  invFun v := ⟨s.coordinates.symm (Multiplicative.ofAdd v.val),
    (fixed_iff s E _).mp (by simp only [MulEquiv.apply_symm_apply]; exact v.property)⟩
  left_inv w := by ext; exact congrArg Subtype.val (s.coordinates.symm_apply_apply w.val)
  right_inv v := by
    apply Subtype.ext
    change (s.coordinates (s.coordinates.symm (Multiplicative.ofAdd v.val))).toAdd = v.val
    rw [s.coordinates.apply_symm_apply]
    rfl

/-- The original natural coordinates identify the centralizer index with the
fixed-space codimension of the actual projected subgroup. -/
theorem fixed_index (E : Subgroup M) :
    (centralizer (E : Set M)).relIndex W =
      2 ^ fixedCodim Model.rho (E.map s.projection) := by
  have hd := fixedCodim_add_finrank Model.rho (E.map s.projection)
  have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 6)) := by
    rw [Nat.card_congr s.coordinates.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 6)) = _
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := BinaryPermutation.natural (Fin 6))
  have hC : Nat.card ((centralizer (E : Set M)).subgroupOf W) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace Model.rho (E.map s.projection)) := by
    rw [Nat.card_congr (fixedEquiv s E)]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace Model.rho (E.map s.projection))
  have hh := ((centralizer (E : Set M)).subgroupOf W).card_mul_index
  rw [hC,hW,← hd,pow_add] at hh
  exact Nat.eq_of_mul_eq_mul_left (n := 2 ^ Module.finrank (ZMod 2)
    (fixedSpace Model.rho (E.map s.projection))) (by positivity)
    (by simpa only [relIndex,mul_comm] using hh)

theorem fixed_quotient_card (E : Subgroup M) :
    Nat.card (W ⧸ (centralizer (E : Set M)).subgroupOf W) =
      2 ^ fixedCodim Model.rho (E.map s.projection) := s.fixed_index E

/-- The literal quotient by the actual two-core has the projected order. -/
theorem image_quotient_card (E : Subgroup M) :
    Nat.card (E ⧸ (pCore 2 M).subgroupOf E) = Nat.card (E.map s.projection) := by
  change (pCore 2 M).relIndex E = _
  rw [← s.projection_kernel]
  exact relIndex_ker (K := E) s.projection

/-- Source 5.0's admissible subgroups, with its weak inequality and no
 elementary-abelian restriction. -/
def smallMover (E : Subgroup M) : Prop :=
  E ≤ R ∧ (centralizer (E : Set M)).relIndex W ≤ Nat.card (E.map s.projection) ∧
    (centralizer (E : Set M)).relIndex W ≤ 4

/-- The literal maximum-order family of Source 5.0. -/
def maximalOffenders : Set (Subgroup M) :=
  {E | s.smallMover E ∧ ∀ F, s.smallMover F → Nat.card F ≤ Nat.card E}

/-- The join denoted J_alpha(T_beta) in Source 5.0. -/
noncomputable def offenderJoin : Subgroup M := sSup s.maximalOffenders

theorem smallMover_iff (E : Subgroup M) :
    s.smallMover E ↔ E ≤ R ∧ 2 ^ fixedCodim Model.rho (E.map s.projection) ≤
      Nat.card (E.map s.projection) ∧ 2 ^ fixedCodim Model.rho (E.map s.projection) ≤ 4 := by
  simp only [smallMover,s.fixed_index]

private theorem card_map (E : Subgroup M) :
    Nat.card (s.projection.ker ⊓ E : Subgroup M) * Nat.card (E.map s.projection) =
      Nat.card E := by
  rw [← relIndex_ker]
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup M) (s.projection.ker ⊓ E) E bot_le inf_le_right

private theorem kernel_le : s.projection.ker ≤ R := by
  rw [s.projection_kernel]
  exact s.core_le

private theorem full_preimage_le (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) (i : Fin 3) :
    (SmallImages.plane g i).comap s.projection ≤ R := by
  exact (comap_mono ((SmallImages.plane_le g i).trans_eq hR.symm)).trans_eq
    (comap_map_eq_self (kernel_le s))

private theorem full_preimage_image (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) (i : Fin 3) :
    ((SmallImages.plane g i).comap s.projection).map s.projection = SmallImages.plane g i :=
  map_comap_eq_self ((SmallImages.plane_le g i).trans (hR ▸ map_le_range s.projection R))

private theorem full_preimage_card (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) (i : Fin 3) :
    Nat.card ((SmallImages.plane g i).comap s.projection) = Nat.card s.projection.ker * 4 := by
  rw [← card_map s,inf_eq_left.mpr (ker_le_comap _ _),full_preimage_image s g hR,
    SmallImages.plane_card_conjugate]

private theorem smallMover_image (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E : Subgroup M} (hE : s.smallMover E) :
    E.map s.projection = ⊥ ∨ E.map s.projection = last.map (MulAut.conj g).toMonoidHom ∨
      ∃ i : Fin 3, E.map s.projection = SmallImages.plane g i := by
  have h := (s.smallMover_iff E).mp hE
  exact (SmallImages.admissible_iff_conjugate g ((map_mono h.1).trans_eq hR)).mp h.2

variable [Finite M]

private theorem smallMover_card_le (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E : Subgroup M} (hE : s.smallMover E) :
    Nat.card E ≤ Nat.card s.projection.ker * 4 := by
  have hi : Nat.card (E.map s.projection) ≤ 4 := by
    rcases smallMover_image s g hR hE with he | he | ⟨i,he⟩
    · rw [he,card_bot]; omega
    · rw [he,card_map_of_injective (MulAut.conj g).injective,card_last]; omega
    · rw [he,SmallImages.plane_card_conjugate]
  rw [← card_map s]
  exact Nat.mul_le_mul (card_le_of_le inf_le_left) hi

omit [Finite M] in
private theorem full_preimage_smallMover (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) (i : Fin 3) :
    s.smallMover ((SmallImages.plane g i).comap s.projection) := by
  apply (s.smallMover_iff _).mpr
  rw [full_preimage_image s g hR,SmallImages.plane_codim,SmallImages.plane_card_conjugate]
  exact ⟨full_preimage_le s g hR i,by norm_num,by norm_num⟩

/-- The maximum-order source family consists exactly of the full preimages
of the three marked mixed planes. -/
theorem mem_maximalOffenders_iff (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) (E : Subgroup M) :
    E ∈ s.maximalOffenders ↔ ∃ i : Fin 3, E = (SmallImages.plane g i).comap s.projection := by
  constructor
  · rintro ⟨hE,hm⟩
    have hlarge : Nat.card s.projection.ker * 4 ≤ Nat.card E := by
      rw [← full_preimage_card s g hR 0]
      exact hm _ (full_preimage_smallMover s g hR 0)
    rcases smallMover_image s g hR hE with he | he | ⟨i,he⟩
    · have hc := card_map s E
      rw [he,card_bot,mul_one] at hc
      have hk := card_le_of_le (show s.projection.ker ⊓ E ≤ s.projection.ker from inf_le_left)
      have hp : 0 < Nat.card s.projection.ker := Nat.card_pos
      omega
    · have hc := card_map s E
      rw [he,card_map_of_injective (MulAut.conj g).injective,card_last] at hc
      have hk := card_le_of_le (show s.projection.ker ⊓ E ≤ s.projection.ker from inf_le_left)
      have hp : 0 < Nat.card s.projection.ker := Nat.card_pos
      omega
    · refine ⟨i,eq_of_le_of_card_ge ?_ ?_⟩
      · exact map_le_iff_le_comap.mp he.le
      · rw [full_preimage_card s g hR]
        exact hlarge
  · rintro ⟨i,rfl⟩
    refine ⟨full_preimage_smallMover s g hR i,fun F hF => ?_⟩
    rw [full_preimage_card s g hR]
    exact smallMover_card_le s g hR hF

theorem maximalOffender_kernel_le (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E : Subgroup M} (hE : E ∈ s.maximalOffenders) : pCore 2 M ≤ E := by
  obtain ⟨i,rfl⟩ := (s.mem_maximalOffenders_iff g hR E).mp hE
  rw [← s.projection_kernel]
  exact ker_le_comap _ _

theorem maximalOffender_image (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E : Subgroup M} (hE : E ∈ s.maximalOffenders) :
    Nat.card (E.map s.projection) = 4 ∧ (centralizer (E : Set M)).relIndex W = 4 := by
  obtain ⟨i,rfl⟩ := (s.mem_maximalOffenders_iff g hR E).mp hE
  rw [s.fixed_index,full_preimage_image s g hR,SmallImages.plane_card_conjugate,SmallImages.plane_codim]
  norm_num

/-- The full source family generates the actual radical. -/
theorem offenderJoin_eq (g : Model.S) (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom) : s.offenderJoin = R := by
  apply le_antisymm (sSup_le fun E hE => hE.1.1)
  have hp (i : Fin 3) : (SmallImages.plane g i).comap s.projection ≤ s.offenderJoin :=
    le_sSup ((s.mem_maximalOffenders_iff g hR _).mpr ⟨i,rfl⟩)
  have hj : (SmallImages.plane g 0).comap s.projection ⊔
      (SmallImages.plane g 1).comap s.projection = R := by
    rw [comap_sup_eq_of_le_range _
      ((SmallImages.plane_le g 0).trans (hR ▸ map_le_range s.projection R))
      ((SmallImages.plane_le g 1).trans (hR ▸ map_le_range s.projection R))]
    rw [SmallImages.planes_generate,← hR,comap_map_eq_self (kernel_le s)]
  exact hj.ge.trans (sup_le (hp 0) (hp 1))

theorem maximalOffender_card (g : Model.S)
    (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E : Subgroup M} (hE : E ∈ s.maximalOffenders) :
    Nat.card E = Nat.card (pCore 2 M) * 4 := by
  obtain ⟨i,rfl⟩ := (s.mem_maximalOffenders_iff g hR E).mp hE
  rw [full_preimage_card s g hR,s.projection_kernel]

omit [Finite M] in
theorem lineMover_image (g : Model.S)
    (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E : Subgroup M} (hER : E ≤ R)
    (hcard : Nat.card (E.map s.projection) = 2)
    (hfixed : (centralizer (E : Set M)).relIndex W = 2) :
    E.map s.projection = last.map (MulAut.conj g).toMonoidHom := by
  have hE : s.smallMover E := ⟨hER,by omega,by omega⟩
  rcases smallMover_image s g hR hE with he | he | ⟨i,he⟩
  · rw [he,card_bot] at hcard
    omega
  · exact he
  · rw [he,SmallImages.plane_card_conjugate] at hcard
    omega

/-- Source 5.1 for the full point-core branch: the source family cannot be
 generated by two line movers, even if these movers are not maximum-order. -/
theorem offenderJoin_ne_sup_of_lineMovers (g : Model.S)
    (hR : R.map s.projection = Model.E.map (MulAut.conj g).toMonoidHom)
    {E₁ E₂ : Subgroup M} (h₁ : E₁ ≤ R) (h₂ : E₂ ≤ R)
    (hc₁ : Nat.card (E₁.map s.projection) = 2)
    (hc₂ : Nat.card (E₂.map s.projection) = 2)
    (hf₁ : (centralizer (E₁ : Set M)).relIndex W = 2)
    (hf₂ : (centralizer (E₂ : Set M)).relIndex W = 2) :
    s.offenderJoin ≠ E₁ ⊔ E₂ := by
  intro heq
  rw [s.offenderJoin_eq g hR] at heq
  have hh := congrArg (fun E : Subgroup M => E.map s.projection) heq
  rw [hR,Subgroup.map_sup,s.lineMover_image g hR h₁ hc₁ hf₁,
    s.lineMover_image g hR h₂ hc₂ hf₂,sup_idem] at hh
  have hc := congrArg (fun E : Subgroup Model.S => Nat.card E) hh
  rw [card_map_of_injective (MulAut.conj g).injective,
    card_map_of_injective (MulAut.conj g).injective,card_exceptional,card_last] at hc
  omega

end Source
namespace SourceData
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The maximum-order family of the literal characteristic replacement has
 join equal to its actual radical and plane images in the inherited marking. -/
theorem reducedSource_maximalOffenders (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : c.radical.map ((originalSource d h).reduce c).projection =
      Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom) :
    ((originalSource d h).reduce c).offenderJoin = c.radical ∧
      ∀ E ∈ ((originalSource d h).reduce c).maximalOffenders,
        pCore 2 c.overgroup ≤ E ∧
        Nat.card (E.map ((originalSource d h).reduce c).projection) = 4 ∧
        (centralizer (E : Set c.overgroup)).relIndex
          ((V.subgroupOf (L ⊔ d.B)).subgroupOf c.overgroup) = 4 := by
  let s := (originalSource d h).reduce c
  refine ⟨s.offenderJoin_eq d.relabeler.val⁻¹ hfull,fun E hE => ?_⟩
  exact ⟨s.maximalOffender_kernel_le d.relabeler.val⁻¹ hfull hE,
    s.maximalOffender_image d.relabeler.val⁻¹ hfull hE⟩

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
