module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySetup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryProduct
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Assembly
public import Theory.GroupTheory.PCoreImage

/-!
# The G.2.3 core geometry of the escaping natural closure

The original natural model L/O₂(L) ≃ SL₂(F) is transported to the literal
L-image in LT/O₂(LT), with its representative formula preserved.
Nonabelianness of U makes its star image nontrivial. The established G.2.1
hypothesis, Frattini bound and closure comparison then supply G.2.3.

This proves L₁ = LU, the exact product of the two relative centralizers
forming O₂(L₁), the elementary central intersection E, and normalization
of O₂(L₁) by LT. Disjointness of the opposite field lines and the moving
pair give both crossed fixed-space identities required by 6.1.26.
Thus the existing escape geometry can be built with only the later
natural-section and index claims, in addition to n=2 and a moving pair.

The initial natural action, source nonabelianness, parameter reduction,
section multiplicity and marked PSL₂ prime component remain obligations
of qt-d-1222-rankone-recognition-natural. This module does not assert the
unconditional 6.1.27 conclusion or a quotient decomposition.

Source: Aschbacher–Smith, 6.1.20–21 and 6.1.26, printed pp.675–676,
678–679, using G.2.1–3, printed pp.332–334.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise
open Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces
open ChapterG.Section02.RankOneHigherFields
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The original quotient L/O₂(L) is exactly the L-image in LT/O₂(LT). -/
theorem natural_escape_star_kernel
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    (starProjection (naturalEscapeSetup (T : Subgroup G) L V)).ker = pCore 2 L := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  have hm : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer h.sylow_normalizes_L)
  ext l
  have he : l ∈ (starProjection D).ker ↔
      inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l ∈
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
    change starProjection D l = 1 ↔ _
    rw [← Subtype.val_inj]
    exact QuotientGroup.eq_one_iff _
  rw [he]
  constructor
  · intro hl
    have hc : (l : G) ∈ L ⊓ centralizer (layer L V : Set G) :=
      ⟨l.property, local_core_centralizes_layer h (mem_map_of_mem _ hl)⟩
    rw [natural_centralizer_eq_core hnatural] at hc
    exact (mem_map_iff_mem L.subtype_injective).mp hc
  · intro hl
    have hc := hm (mem_map_of_mem L.subtype hl)
    exact (mem_map_iff_mem (L ⊔ (T : Subgroup G)).subtype_injective).mp hc

/-- Nonabelianness of the actual closure makes its literal star image nontrivial. -/
theorem natural_escape_star_nontrivial
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G)) :
    let D := naturalEscapeSetup (T : Subgroup G) L V
    D.star D.U ≠ ⊥ := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  have hU : D.U = Escape.U (T : Subgroup G) L V := natural_escape_normalizer_span h hE hNS
  change D.star D.U ≠ ⊥
  intro hz
  have hUC : Escape.U (T : Subgroup G) L V ≤ centralizer (layer L V : Set G) := by
    intro u hu
    let x : D.LT := ⟨u, (natural_escape_U_le_sylow h hnatural hu |> mem_sup_right)⟩
    have hx : QuotientGroup.mk' (pCore 2 D.LT) x ∈ D.star D.U :=
      mem_map_of_mem _ (show x ∈ D.U.subgroupOf D.LT from hU.symm ▸ hu)
    rw [hz, mem_bot] at hx
    exact local_core_centralizes_layer h (mem_map_of_mem D.LT.subtype
      ((QuotientGroup.eq_one_iff x).mp hx))
  obtain ⟨g, hg, hmove⟩ := natural_escape_exists_pair hnon
  exact hmove ((natural_escape_pair_normalizes h hnatural hg).1.trans hUC)

/-- Construct the G.2.3 marking through the actual star quotient. The initial
natural action and nonabelianness are the two earlier source inputs. -/
theorem natural_escape_G2_marking
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty (Hypothesis (naturalEscapeSetup (T : Subgroup G) L V) F n l) := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  have hbase := natural_escape_G2_hypothesis h hnatural
  have hspan := natural_escape_point_span h hnatural
  have hne := natural_escape_star_nontrivial h hnatural hE hNS hnon
  have hk := natural_escape_star_kernel h hnatural
  have hcard := (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
  obtain ⟨F, _, _, _, hF, e, f, hf⟩ := hnatural
  change ∀ (x : L) (v : layer L V), (f.symm (Multiplicative.ofAdd
    ((e (QuotientGroup.mk' (pCore 2 L) x)).val *ᵥ (f v).toAdd)) : G) =
      (x : G) * (v : G) * (x : G)⁻¹ at hf
  let q : L →* D.star D.L := starProjection D
  change q.ker = pCore 2 L at hk
  let e₀ : (L ⧸ pCore 2 L) ≃* D.star D.L :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q (starProjection_surjective D))
  let em : D.star D.L ≃* SL(2,F) := e₀.symm.trans e
  have hem (x : L) : em (starProjection D x) = e (QuotientGroup.mk' (pCore 2 L) x) := by
    apply congrArg e
    change e₀.symm (starProjection D x) = QuotientGroup.mk' (pCore 2 L) x
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    rfl
  let P := sylowSpace (T : Subgroup G) e
  have hP : P.toAddSubgroup = coordinateSpace f (ZS (T : Subgroup G) L V) :=
    AddSubgroup.ext (mem_sylowSpace_iff (T : Subgroup G) e f hf)
  have hc : Nat.card P = Nat.card F := by
    change Nat.card P.toAddSubgroup = Nat.card F
    rw [hP, coordinateSpace_card f (show ZS (T : Subgroup G) L V ≤ layer L V from inf_le_left), hF]
    exact hcard
  have hd : Module.finrank F P = 1 := by
    apply Nat.pow_right_injective (Finite.one_lt_card (α := F))
    change Nat.card F ^ Module.finrank F P = Nat.card F ^ 1
    rw [← Module.natCard_eq_pow_finrank, hc, pow_one]
  have hequiv (x : L) (v w : layer L V)
      (hw : (w : G) = (x : G) * (v : G) * (x : G)⁻¹) :
      (f w).toAdd = (em (starProjection D x)).val *ᵥ (f v).toAdd := by
    rw [hem]
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    simpa only [ofAdd_toAdd, f.symm_apply_apply] using hw.trans (hf x v).symm
  have hpoint (v : layer L V) : (v : G) ∈ ZS (T : Subgroup G) L V ↔ (f v).toAdd ∈ P := by
    change (v : G) ∈ ZS (T : Subgroup G) L V ↔ (f v).toAdd ∈ P.toAddSubgroup
    rw [hP]
    simp
  exact ⟨F, inferInstance, inferInstance, ⟨{
    setup := hbase
    exponent_gt_one := h.n_gt_one
    field_card := hF
    span_eq := hspan
    model := em
    coordinates := f
    equivariant := fun x v => hequiv x v _ rfl
    point := P
    point_dimension := hd
    point_mem := hpoint
    star_U_ne_bot := hne
    g_mem := hl
    g_not_normalizing := hlout }⟩⟩


/-- Source 6.1.21's generation, core product, and elementary central
intersection, with the literal right conjugate and original two-core.
Only the earlier natural action and nonabelianness remain explicit. -/
theorem natural_escape_core_geometry
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    Escape.L1 (T : Subgroup G) L V l = L ⊔ Escape.U (T : Subgroup G) L V ∧
    Escape.R (T : Subgroup G) L V l =
      (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) ⊔
        ((Escape.U (T : Subgroup G) L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
          centralizer (layer L V : Set G)) ∧
    IsElementaryAbelian 2 (Escape.E (T : Subgroup G) L V l) ∧
    ⁅Escape.L1 (T : Subgroup G) L V l, Escape.E (T : Subgroup G) L V l⁆ ≤ layer L V ∧
    L ⊔ (T : Subgroup G) ≤ normalizer (Escape.R (T : Subgroup G) L V l : Set G) := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  obtain ⟨F, _, _, ⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS hnon hl hlout
  obtain ⟨hU,hI,hR,hE'⟩ := natural_escape_G2_constructions h hE hNS l
  have hut : D.U ≤ D.T := by
    rw [hU]
    exact natural_escape_U_le_sylow h hnatural
  have hphi := (natural_escape_G2_hypothesis h hnatural).frattini_U_le_point
  have hgen := d.I_eq_LU hut hphi
  have hcore := d.S_eq_WProduct_of_source hut hphi
  have hseries := d.series hut hphi
  have hnormal := d.LT_normalizes_I_of_star hut (d.star_I_eq_star_L hut hphi).ge
  have hW : D.W l = Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G) := by
    change D.U ⊓ D.S l = _
    rw [d.S_eq_star_kernel hut hphi, ← inf_assoc, inf_eq_left.mpr (show D.U ≤ D.I l from le_sup_left)]
    change D.U ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [← local_layer_centralizer_eq_core h hnatural, ← inf_assoc,
      inf_eq_left.mpr (show D.U ≤ L ⊔ (T : Subgroup G) from hut.trans le_sup_right), hU]
  have hW' : ChapterG.Section02.Setup.conjugate (D.W l) l =
      ((Escape.U (T : Subgroup G) L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
        centralizer (layer L V : Set G)) := by
    rw [ChapterG.Section02.RankOneHigherFields.Hypothesis.conjugate_W (d.g_mem_I hut hphi),
      d.S_eq_star_kernel hut hphi, ← inf_assoc,
      inf_eq_left.mpr (show ChapterG.Section02.Setup.conjugate D.U l ≤ D.I l from le_sup_right)]
    change ChapterG.Section02.Setup.conjugate D.U l ⊓
      (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [← local_layer_centralizer_eq_core h hnatural, ← inf_assoc,
      inf_eq_left.mpr (show ChapterG.Section02.Setup.conjugate D.U l ≤ L ⊔ (T : Subgroup G) from
        (show ChapterG.Section02.Setup.conjugate D.U l ≤ D.I l from le_sup_right).trans (d.I_le_LT hut)), hU]
    rfl
  change D.I l = D.L ⊔ D.U at hgen
  rw [hI,hU] at hgen
  change D.S l = D.W l ⊔ ChapterG.Section02.Setup.conjugate (D.W l) l at hcore
  rw [hR,hW',hW] at hcore
  refine ⟨hgen,hcore,?_,?_,?_⟩
  · have helem := hseries.2.2.2.2.2.2.2
    change IsElementaryAbelian 2 (D.S₂ l) at helem
    rw [hE'] at helem
    exact helem
  · have hc := hseries.2.2.2.2.2.2.1
    rw [commutator_comm,hI,hE'] at hc
    exact hc
  · have hn := hnormal.trans (normalizer_le_normalizer_characteristic_image
      (D.I l) (pCore 2 (D.I l)))
    change D.LT ≤ normalizer (D.S l : Set G) at hn
    rwa [hR] at hn


private theorem nonabelian_of_moving_pair
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    {g : G} (hg : g ∈ Escape.I (T : Subgroup G) L V)
    (hmove : ¬ (layer L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (layer L V : Set G)) :
    ¬ Escape.U (T : Subgroup G) L V ≤ centralizer (Escape.U (T : Subgroup G) L V : Set G) := by
  intro hab
  apply hmove
  exact ((natural_escape_pair_normalizes h hnatural
    ((Escape.I (T : Subgroup G) L V).inv_mem hg)).1.trans hab).trans
      (centralizer_le (Escape.layer_le_U _ _ _))

/-- The two crossed fixed spaces in 6.1.26 vanish. The moving-pair line
identities and the disjoint opposite field lines discharge both premises. -/
theorem natural_escape_crossed_fixed_spaces
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    {g l : G} (hg : g ∈ Escape.I (T : Subgroup G) L V) (hl : l ∈ L)
    (hlout : l ∉ Escape.H (T : Subgroup G) L V)
    (hmove : ¬ (layer L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (layer L V : Set G)) :
    ZS (T : Subgroup G) L V ⊓ centralizer
      ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥ ∧
    (ZS (T : Subgroup G) L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥ := by
  let B := layer L V
  let Z := ZS (T : Subgroup G) L V
  let A := B.map (MulAut.conj g⁻¹).toMonoidHom
  let Z' := Z.map (MulAut.conj l⁻¹).toMonoidHom
  obtain ⟨F, _, _, ⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS
    (nonabelian_of_moving_pair h hnatural hg hmove) hl hlout
  have hdis : Z ⊓ Z' = ⊥ := disjoint_iff.mp d.point_disjoint
  have hB : B.map (MulAut.conj l⁻¹).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right V L (L.inv_mem hl))
  have hZ' : Z' ≤ B := (map_mono (show Z ≤ B from inf_le_left)).trans_eq hB
  have hfix : B ⊓ centralizer (A : Set G) = Z :=
    (natural_escape_pair_lines h hnatural hE hs
      ((Escape.I (T : Subgroup G) L V).inv_mem hg) hmove).1
  have hmap := congrArg (fun K : Subgroup G => K.map (MulAut.conj l⁻¹).toMonoidHom) hfix
  rw [map_inf _ _ _ (MulAut.conj l⁻¹).injective, hB,
    Theory.Quasithin.map_centralizer] at hmap
  have hA : A.map (MulAut.conj l⁻¹).toMonoidHom =
      B.map (MulAut.conj (g * l)⁻¹).toMonoidHom := by
    rw [fusion_map_conj_mul, _root_.mul_inv_rev]
  rw [hA] at hmap
  constructor
  · calc
      Z ⊓ centralizer (B.map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) =
          Z ⊓ (B ⊓ centralizer (B.map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G)) := by
            rw [← inf_assoc, inf_eq_left.mpr (show Z ≤ B from inf_le_left)]
      _ = ⊥ := by rw [hmap]; exact hdis
  · calc
      Z' ⊓ centralizer (A : Set G) = Z' ⊓ (B ⊓ centralizer (A : Set G)) := by
        rw [← inf_assoc, inf_eq_left.mpr hZ']
      _ = ⊥ := by rw [hfix, inf_comm]; exact hdis

/-- All geometric identities in the size argument now follow from G.2.3
and the moving pair. Only the later natural-section and multiplicity inputs
remain, alongside the earlier n=2 and moving-pair conclusions. -/
theorem natural_escape_geometry_of_section
    (h : Hypothesis611 κ T L M V 2)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = 2)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    {g l : G} (hg : g ∈ Escape.I (T : Subgroup G) L V) (hl : l ∈ L)
    (hlout : l ∉ Escape.H (T : Subgroup G) L V)
    (hmove : ¬ (layer L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (layer L V : Set G))
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L V l)
      (Escape.R (T : Subgroup G) L V l) (Escape.E (T : Subgroup G) L V l))
    (hindex : (Escape.E (T : Subgroup G) L V l).relIndex
      (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) = 4) :
    Nonempty (NaturalEscape.Geometry (T : Subgroup G) L V) := by
  obtain ⟨hgen,hcore,helem,hcentral,_⟩ := natural_escape_core_geometry h hnatural hE hNS
    (nonabelian_of_moving_pair h hnatural hg hmove) hl hlout
  let := helem
  obtain ⟨hfixedR,hfixedL⟩ := natural_escape_crossed_fixed_spaces h hnatural hE hs hNS hg hl hlout hmove
  exact natural_escape_geometry_of_pair h hnatural hE hs hg hl hlout hmove hgen
    (le_centralizer _) hcore hcentral hfixedR hfixedL hsection hindex

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
