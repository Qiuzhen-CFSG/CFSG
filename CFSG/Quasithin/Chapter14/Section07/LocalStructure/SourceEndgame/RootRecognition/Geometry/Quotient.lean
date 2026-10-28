module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Applications
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.QuotientAction.ProjectiveOrbit.Geometry
public import Theory.Representation.BinaryConjugationSection.Canonical
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The literal quotient action and original marked root geometry

Starting with the original marked root images, the existing lifting and Sylow
arguments identify the product with P = O₂(K). Its intersection E is a normal
two-subgroup of K, hence is contained in P. Both root factors are normal in P;
their commutators and squares lie in E. Consequently the literal P/E is an
elementary abelian group, with a canonical action through the SAME qK.

The marked image data below are an output interface for the separate image
calculation, not earlier-source assumptions. No action or recognition witness
is stored in that interface. The marked-image branch of 14.7.73 must construct
it from the genuine earlier setup and 71/72. The projective orbit map then
satisfies every G.1.3 condition. Only the universal recognition implication
is used to obtain natural copies. The separate multiplicity-one argument
must still determine their number; a one-copy adapter feeds the original
`source_quotient_outputs` with every preceding group premise discharged.

Source: Aschbacher–Smith 14.7.73, printed pp.1076–1077 (PDF pp.1093–1094).
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry
open Chapter12.Section08 CriticalFusion.Source
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- Only the universal G.1.3 decomposition implication is retained.
Unlike the broader rank-one recognition interface, this premise does not
include the separate G.1.5(2) fixed-space conclusion. -/
def NaturalRecognition : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (σ : Representation (ZMod 2) SL2FourNatural.SL M)
    (φ : Point SL2FourNatural.F → Submodule (ZMod 2) M),
    Criterion σ φ → ∃ s : ℕ, NaturalCopies σ s

/-- Outputs to be proved by the marked-image branch of 14.7.73, for the original k.
In particular none of these fields is assumed by the final source theorem. -/
structure MarkedImages (d : Data T L V F W) (k : K F) where
  le_residual : S L F ≤ K F
  sylow : Sylow 2 SL2FourNatural.SL
  sylow_image : ((S L F).subgroupOf (K F)).map (qK d) = (sylow : Subgroup _)
  pair_image : ((S L F ⊔ (S L F).conjBy ((k : G)⁻¹)).subgroupOf (K F)).map
    (qK d) = ⊤
  point : Point SL2FourNatural.F
  root_image : ((S L F).subgroupOf (K F)).map (qK d) = rootGroup SL2FourNatural.F point.val
  point_moved : point.val ≠ point.val.map (Representation.specialLinearNatural 2 (qK d k⁻¹))
  normalizer_lift : ∀ a ∈ normalizer (rootGroup SL2FourNatural.F point.val : Set SL2FourNatural.SL),
    ∃ l : K F, qK d l = a ∧ (l : G) ∈ normalizer (S L F : Set G)

variable (d : Data T L V F W) (k : K F)
  (hS : S L F = L.pCoreIn 2)
  (hPhi : (frattini (S L F)).map (S L F).subtype = V)
  (hTL : (T : Subgroup G) ≤ normalizer L)
  (m : MarkedImages d k)

include hS hPhi in
/-- The actual 72 Frattini identity gives the needed commutator bound. -/
theorem derived_le_U : ⁅S L F, S L F⁆ ≤ F.U :=
  derived_le_of_frattini_image_le (hS.symm ▸ isPGroup_pCoreIn 2 L)
    (hPhi.le.trans (Data.V_le_U F))

include hS hTL m in
/-- Generation is lifted through qK's two-kernel, not assumed in K. -/
theorem generation : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹) :=
  source_generation d k m.le_residual (QH_normalizes_S hS hTL) m.pair_image

include hS hPhi hTL m in
/-- The literal product candidate is the original two-core. -/
theorem product_eq_core : P₀ L F k = (K F).pCoreIn 2 :=
  (source_product_eq_core d k m.le_residual (QH_normalizes_S hS hTL)
    (generation d k hS hTL m) (derived_le_U hS hPhi) (U_le_QH d)
    m.sylow m.sylow_image).2

include hS hPhi hTL m in
/-- E is inside P by relative normality and its two-group structure. -/
theorem intersection_le_core : E L F k ≤ (K F).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
    ((hS.symm ▸ isPGroup_pCoreIn 2 L).of_injective
      (inclusion (inf_le_left : E L F k ≤ S L F)) (inclusion_injective _))
    (inf_le_left.trans m.le_residual)
  exact K_normalizes_E d k (generation d k hS hTL m) (derived_le_U hS hPhi)

include hS hPhi hTL m in
/-- Perfectness and the actual Sylow lift generate P modulo U before recognition. -/
theorem core_commutator_generation :
    ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2 := by
  let := K_perfect d
  let : (((K F).pCoreIn 2).subgroupOf (K F)).Normal :=
    normal_subgroupOf_of_le_normalizer ((K F).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _))
  let : (F.U.subgroupOf (K F)).Normal := normal_subgroupOf_of_le_normalizer
    ((K_le_H F).trans d.conjugationSection.normalized)
  obtain ⟨R, hR⟩ := source_sylow d m.le_residual m.sylow m.sylow_image
  exact commutator_generation_of_source_sylow (K F) ((K F).pCoreIn 2)
    (S L F) F.U (pCoreIn_le 2 _) m.le_residual
    ((U_le_E d k).trans (intersection_le_core d k hS hPhi hTL m))
    (isPGroup_pCoreIn 2 _) R hR (derived_le_U hS hPhi)

include hS hPhi hTL m in
/-- Normality for the literal quotient P/E. -/
theorem intersection_normal : ((E L F k).subgroupOf ((K F).pCoreIn 2)).Normal :=
  normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 _).trans
    (K_normalizes_E d k (generation d k hS hTL m) (derived_le_U hS hPhi)))

include hS hPhi hTL m in
/-- The source two factors generate P and meet in precisely E. -/
theorem core_factors :
    (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
      ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
    E L F k = (S L F ⊓ (K F).pCoreIn 2) ⊓
      ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) := by
  have hi (A : Subgroup G) (hAK : A ≤ K F) :
      A ⊓ F.H.pCoreIn 2 = A ⊓ (K F).pCoreIn 2 := by
    rw [K_core_eq_intersection]
    exact le_antisymm (fun _ h => ⟨h.1, hAK h.1, h.2⟩) (fun _ h => ⟨h.1, h.2.2⟩)
  have hgen := generation d k hS hTL m
  have hp := product_eq_core d k hS hPhi hTL m
  unfold P₀ at hp
  rw [hi _ m.le_residual, hi _ (le_sup_right.trans hgen.ge)] at hp
  refine ⟨hp.symm, le_antisymm ?_ ?_⟩
  · intro x hx
    have hxp := intersection_le_core d k hS hPhi hTL m hx
    exact ⟨⟨hx.1, hxp⟩, hx.2, hxp⟩
  · exact fun _ h => ⟨h.1.1, h.2.1⟩

omit [Finite G] in
include hS hTL in
/-- The core normalizes the first root before the natural module is recognized. -/
theorem core_normalizes_root : (K F).pCoreIn 2 ≤ normalizer (S L F : Set G) :=
  (K_core_eq_intersection.le.trans inf_le_right).trans (QH_normalizes_S hS hTL)

omit [Finite G] in
include hS hTL in
/-- Right conjugation preserves the core and transports its normalizer bound. -/
theorem core_normalizes_conjugate :
    (K F).pCoreIn 2 ≤ normalizer ((S L F).conjBy ((k : G)⁻¹) : Set G) := by
  have hn : K F ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
    (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)
  have he : ((K F).pCoreIn 2).map (MulAut.conj ((k : G)⁻¹)).toMonoidHom =
      (K F).pCoreIn 2 := mem_normalizer_iff_map_conj_eq.mp (hn ((K F).inv_mem k.property))
  have hh := (map_mono (f := (MulAut.conj ((k : G)⁻¹)).toMonoidHom)
    (core_normalizes_root (F := F) hS hTL)).trans
      ((S L F).le_normalizer_map (MulAut.conj ((k : G)⁻¹)).toMonoidHom)
  rwa [he] at hh

include hS hPhi hTL m in
/-- P/E is elementary from the two normal factors and their square bounds. -/
theorem quotient_elementary :
    let := intersection_normal d k hS hPhi hTL m
    IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2)) := by
  let := intersection_normal d k hS hPhi hTL m
  let P := (K F).pCoreIn 2
  let A := S L F ⊓ P
  let B := (S L F).conjBy ((k : G)⁻¹) ⊓ P
  let N := (E L F k).subgroupOf P
  let q := QuotientGroup.mk' N
  have hPA : P ≤ normalizer A :=
    (le_inf (core_normalizes_root (F := F) hS hTL) P.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hPB : P ≤ normalizer B :=
    (le_inf (core_normalizes_conjugate (F := F) k hS hTL) P.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hprod : P = A ⊔ B := (core_factors d k hS hPhi hTL m).1
  have hinter : E L F k = A ⊓ B := (core_factors d k hS hPhi hTL m).2
  have hcomm : ⁅A, B⁆ ≤ E L F k := by
    rw [hinter]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hPA))
      (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hPB))
  have hsquare : ∀ s ∈ S L F, s ^ 2 ∈ F.U := by
    let : Fact (IsPGroup 2 (S L F)) := ⟨hS.symm ▸ isPGroup_pCoreIn 2 L⟩
    intro s hs
    exact Data.V_le_U F (hPhi ▸ (show s ^ 2 ∈ (frattini (S L F)).map (S L F).subtype from
      ⟨(⟨s, hs⟩ : S L F) ^ 2, pth_power_mem_frattini_of_isPGroup (p := 2) _, rfl⟩))
  have hsqA : ∀ a ∈ A, a ^ 2 ∈ E L F k := fun a ha => U_le_E d k (hsquare a ha.1)
  have hsqB : ∀ b ∈ B, b ^ 2 ∈ E L F k := by
    rintro b ⟨⟨s, hs, rfl⟩, _⟩
    apply U_le_E d k
    have hu := mem_map_of_mem (MulAut.conj ((k : G)⁻¹)).toMonoidHom (hsquare s hs)
    have he : F.U.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom = F.U :=
      mem_normalizer_iff_map_conj_eq.mp (d.conjugationSection.normalized
      (K_le_H F ((K F).inv_mem k.property)))
    rw [he] at hu
    simpa only [map_pow] using hu
  have hsquares : ∀ x : P ⧸ N, x ^ 2 = 1 := by
    intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hm : (p : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B (inf_le_right.trans hPA), ← hprod]
      exact p.property
    obtain ⟨a, ha, b, hb, hab⟩ := hm
    let aP : P := ⟨a, ha.2⟩
    let bP : P := ⟨b, hb.2⟩
    have hp : aP * bP = p := Subtype.ext hab
    have ha2 : (q aP) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqA a ha)
    have hb2 : (q bP) ^ 2 = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hsqB b hb)
    have hc : Commute (q aP) (q bP) := by
      change q aP * q bP = q bP * q aP
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr (hcomm (commutator_mem_commutator ha hb))
    change (q p) ^ 2 = 1
    rw [← hp, map_mul, hc.mul_pow, ha2, hb2, mul_one]
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hsquares x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquares }


include hS hPhi hTL m in
/-- The canonical P/E coordinates, complementary roots and their marked action. -/
theorem exists_quotient_action :
    let := intersection_normal d k hS hPhi hTL m
    let := quotient_elementary d k hS hPhi hTL m
    ∃ (σ : Representation (ZMod 2) SL2FourNatural.SL
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2))))
      (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k) (σ.comp (qK d))),
      (∀ p : (K F).pCoreIn 2, (c.coordinates p).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((E L F k).subgroupOf ((K F).pCoreIn 2)) p)) ∧
      IsCompl (c.imageSpace (S L F ⊓ (K F).pCoreIn 2))
        (c.imageSpace ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2)) ∧
      c.imageSpace ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) =
        (c.imageSpace (S L F ⊓ (K F).pCoreIn 2)).map (σ (qK d k⁻¹)) ∧
      (∀ a ∈ rootGroup SL2FourNatural.F m.point.val,
        LinearMap.range (σ a - 1) ≤ c.imageSpace (S L F ⊓ (K F).pCoreIn 2) ∧
        ∀ v ∈ c.imageSpace (S L F ⊓ (K F).pCoreIn 2), σ a v = v) ∧
      ∀ a ∈ normalizer (rootGroup SL2FourNatural.F m.point.val : Set SL2FourNatural.SL),
        (c.imageSpace (S L F ⊓ (K F).pCoreIn 2)).map (σ a) =
          c.imageSpace (S L F ⊓ (K F).pCoreIn 2) := by
  let := intersection_normal d k hS hPhi hTL m
  let := quotient_elementary d k hS hPhi hTL m
  let P := (K F).pCoreIn 2
  have hNP : K F ≤ normalizer (P : Set G) :=
    (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _)
  have hNE := K_normalizes_E d k (generation d k hS hTL m) (derived_le_U hS hPhi)
  obtain ⟨σ, c, hc⟩ := BinaryConjugationSection.exists_canonical (K F) P (E L F k)
    (pCoreIn_le 2 _) (intersection_le_core d k hS hPhi hTL m) hNP hNE
    (qK d) (qK_surjective d) (qK_ker d)
  obtain ⟨hprod, hinter⟩ := core_factors d k hS hPhi hTL m
  have hconj : (S L F ⊓ P).conjBy ((k : G)⁻¹) =
      (S L F).conjBy ((k : G)⁻¹) ⊓ P := by
    change (S L F ⊓ P).map (MulAut.conj ((k : G)⁻¹)).toMonoidHom = _
    have hp : P.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp (hNP ((K F).inv_mem k.property))
    rw [Subgroup.map_inf _ _ _ (MulAut.conj ((k : G)⁻¹)).injective, hp]
    rfl
  refine ⟨σ, c, hc, c.isCompl_imageSpace _ _ hprod hinter, ?_, ?_, ?_⟩
  · rw [← hconj]
    exact c.imageSpace_conjBy (S L F ⊓ P) inf_le_right k⁻¹
  · intro a ha
    rw [← m.root_image] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    have hSP : ⁅S L F, P⁆ ≤ S L F ⊓ P :=
      le_inf (le_normalizer_iff_commutator_le_left.mp (core_normalizes_root (F := F) hS hTL))
        (le_normalizer_iff_commutator_le_right.mp (m.le_residual.trans hNP))
    have hSA : ⁅S L F, S L F ⊓ P⁆ ≤ E L F k :=
      ((commutator_mono le_rfl inf_le_left).trans (derived_le_U hS hPhi)).trans (U_le_E d k)
    exact ⟨c.displacement_range_le_imageSpace_of_commutator_le _ _ hSP s hs,
      c.fixed_on_imageSpace_of_commutator_le _ _ hSA s hs⟩
  · intro a ha
    obtain ⟨l, hl, hn⟩ := m.normalizer_lift a ha
    have hnl : (l : G) ∈ normalizer (S L F ⊓ P : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨hn, hNP l.property⟩
    have hh := c.imageSpace_conjBy (S L F ⊓ P) inf_le_right l
    have he : (S L F ⊓ P).conjBy (l : G) = S L F ⊓ P :=
      mem_normalizer_iff_map_conj_eq.mp hnl
    rw [he] at hh
    change c.imageSpace _ = (c.imageSpace _).map (σ (qK d l)) at hh
    rw [hl] at hh
    exact hh.symm

include hS hPhi hTL m in
/-- All G.1.3 conditions for the original literal quotient and original k.
No projective map or natural section is a hypothesis. -/
theorem exists_projective_quotient :
    let := intersection_normal d k hS hPhi hTL m
    let := quotient_elementary d k hS hPhi hTL m
    ∃ (σ : Representation (ZMod 2) SL2FourNatural.SL
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2))))
      (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k) (σ.comp (qK d)))
      (φ : Point SL2FourNatural.F → Submodule (ZMod 2)
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2)))),
      (∀ p : (K F).pCoreIn 2, (c.coordinates p).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((E L F k).subgroupOf ((K F).pCoreIn 2)) p)) ∧
      Criterion σ φ ∧
      φ m.point = c.imageSpace (S L F ⊓ (K F).pCoreIn 2) ∧
      φ (translate (qK d k⁻¹) m.point) =
        c.imageSpace ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) := by
  let := intersection_normal d k hS hPhi hTL m
  let := quotient_elementary d k hS hPhi hTL m
  obtain ⟨σ, c, hc, hcompl, hmove, hroot, hn⟩ := exists_quotient_action d k hS hPhi hTL m
  have hcompl' : IsCompl (c.imageSpace (S L F ⊓ (K F).pCoreIn 2))
      ((c.imageSpace (S L F ⊓ (K F).pCoreIn 2)).map (σ (qK d k⁻¹))) := by
    rw [← hmove]
    exact hcompl
  obtain ⟨φ, hpoint, hφ, hcriterion⟩ := exists_orbit_criterion σ m.point
    (c.imageSpace (S L F ⊓ (K F).pCoreIn 2)) (qK d k⁻¹)
    m.point_moved hcompl' hn hroot
  exact ⟨σ, c, φ, hc, hcriterion, hpoint,
    (hφ (qK d k⁻¹) _ (translate_val _ _)).trans hmove.symm⟩

include hS hPhi hTL m in
/-- The permitted universal G.1.3 implication now applies to the constructed
quotient. The number of natural copies is still to be determined using 71. -/
theorem exists_natural_copies
    (recognition : NaturalRecognition.{u}) :
    let := intersection_normal d k hS hPhi hTL m
    let := quotient_elementary d k hS hPhi hTL m
    ∃ (σ : Representation (ZMod 2) SL2FourNatural.SL
        (Additive ((K F).pCoreIn 2 ⧸ (E L F k).subgroupOf ((K F).pCoreIn 2))))
      (_c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k) (σ.comp (qK d)))
      (s : ℕ), NaturalCopies σ s := by
  let := intersection_normal d k hS hPhi hTL m
  let := quotient_elementary d k hS hPhi hTL m
  obtain ⟨σ, c, φ, _, hcriterion, _, _⟩ := exists_projective_quotient d k hS hPhi hTL m
  obtain ⟨s, hs⟩ := recognition _ σ φ hcriterion
  exact ⟨σ, c, s, hs⟩


variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- One copy in the original marking supplies the required natural section,
with no change to qK or to the subgroup quotient kernel. -/
theorem natural_section_of_one_copy
    (σ : Representation (ZMod 2) SL2FourNatural.SL M)
    (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k) (σ.comp (qK d)))
    (hcopy : NaturalCopies σ 1) :
    Nonempty (BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d))) := by
  obtain ⟨f, hf⟩ : ∃ f : M ≃+ SL2FourNatural.V,
      ∀ a v, f (σ a v) = Matrix.mulVec a.val (f v) := by
    let := ZMod.algebra SL2FourNatural.F 2
    let : Module (ZMod 2) SL2FourNatural.F := Algebra.toModule
    obtain ⟨e, he⟩ := hcopy
    exact ⟨e.toAddEquiv.trans (AddEquiv.funUnique (Fin 1) SL2FourNatural.V),
      fun a v => he a v 0⟩
  let q := (AddMonoidHom.toMultiplicative f.toAddMonoidHom).comp c.coordinates
  refine ⟨{
    section_le := c.section_le
    kernel_le := c.kernel_le
    normalized := c.normalized
    coordinates := q
    onto := ?_
    kernel_eq := ?_
    equivariant := ?_ }⟩
  · intro v
    obtain ⟨w, hw⟩ := f.surjective v.toAdd
    obtain ⟨p, hp⟩ := c.onto (Multiplicative.ofAdd w)
    refine ⟨p, ?_⟩
    change f (c.coordinates p).toAdd = v.toAdd
    rw [hp]
    exact hw
  · ext p
    change f (c.coordinates p).toAdd = 0 ↔ (p : G) ∈ E L F k
    rw [← f.map_zero, f.injective.eq_iff]
    exact c.coordinates_eq_one_iff p
  · intro l p
    change f (c.coordinates _).toAdd =
      SL2FourNatural.naturalRepresentation (qK d l) (f (c.coordinates p).toAdd)
    rw [c.equivariant]
    exact hf (qK d l) (c.coordinates p).toAdd

include hS hPhi hTL m in
/-- Application to the actual elementary/generation consumer. The marked
image producer and the multiplicity-one producer supply the two remaining
inputs; all preceding group premises of `source_quotient_outputs` are derived. -/
theorem source_outputs_of_one_copy
    (σ : Representation (ZMod 2) SL2FourNatural.SL M)
    (c : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k) (σ.comp (qK d)))
    (hcopy : NaturalCopies σ 1) :
    Nonempty (BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d))) ∧
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2)) ∧
      ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2 ∧
      (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
        ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
      ∃ R' : Sylow 2 (K F),
        (R' : Subgroup (K F)).map (K F).subtype = S L F ⊔ (K F).pCoreIn 2 := by
  obtain ⟨n⟩ := natural_section_of_one_copy d k σ c hcopy
  exact ⟨⟨n⟩, source_quotient_outputs d k hS hPhi hTL (generation d k hS hTL m)
    m.sylow m.sylow_image n⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry
