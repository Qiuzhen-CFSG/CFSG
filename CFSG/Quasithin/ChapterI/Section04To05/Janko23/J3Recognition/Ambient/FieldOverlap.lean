module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.Overlap
import Mathlib.Tactic.FinCases

/-!
# Coincident field roots and crossing field involutions

Rebuild both faithful 16:(15:2) embeddings using the compatible natural
plane coordinates. Their base-field translation homomorphisms coincide,
and their common image is exactly the original four-group E.

Fourth-power Frobenius fixes these translations. Its ambient image lies
in C_G(E), whose quotient by R has odd order three, and hence lies in R.
It lies outside its own plane because it belongs to the complement.
Every involution of UT₃(F₄) lies in one of its two planes, so each field
involution belongs to the other original plane. These are actual elements
in G, with the original fourth-power action retained in FieldEmbedding.

This couples the two local field constructions. It does not construct an
opposite sixteen-root or a Weyl element outside the plane normalizers.
Source: Aschbacher, *Sporadic Groups* (1994), 46.14(1–5a), pp.257–258;
Aschbacher–Smith I.4.7(2), p.418.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition.PlaneCoordinates
open Sporadic.Janko3.SourceRecognition.PlaneTransport
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient
open LocalSixteen
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

private theorem center_axis_surjective (P : ReturningPair D)
    (A : Subgroup G) (hEA : P.E ≤ A) (a : A ≃* Plane)
    (hl : ∀ x : P.E, (a (inclusion hEA x)).toAdd 1 = 0) :
    ∀ c : Multiplicative Representation.SL2FourNatural.F,
      ∃ x : P.E, a (inclusion hEA x) = axis c := by
  let q : P.E →* Multiplicative Representation.SL2FourNatural.F :=
    { toFun x := Multiplicative.ofAdd ((a (inclusion hEA x)).toAdd 0)
      map_one' := by simp
      map_mul' x y := by
        change (a (inclusion hEA (x * y))).toAdd 0 =
          (a (inclusion hEA x)).toAdd 0 + (a (inclusion hEA y)).toAdd 0
        rw [map_mul,map_mul]
        rfl }
  have hi : Function.Injective q := by
    intro x y h
    apply Subtype.ext
    have hh : a (inclusion hEA x) = a (inclusion hEA y) := by
      change (a (inclusion hEA x)).toAdd = (a (inclusion hEA y)).toAdd
      funext i
      fin_cases i
      · exact congrArg Multiplicative.toAdd h
      · exact (hl x).trans (hl y).symm
    exact congrArg (fun y : A => (y : G)) (a.injective hh)
  have hc : Nat.card P.E = Nat.card (Multiplicative Representation.SL2FourNatural.F) := by
    rw [P.E_card,Nat.card_congr Multiplicative.toAdd,Nat.card_eq_fintype_card,
      Representation.SL2FourNatural.card_field]
  have hs := ((Nat.bijective_iff_injective_and_card q).mpr ⟨hi,hc⟩).2
  intro c
  obtain ⟨x,hx⟩ := hs c
  refine ⟨x,?_⟩
  change (a (inclusion hEA x)).toAdd = ![c.toAdd,0]
  funext i
  fin_cases i
  · exact congrArg Multiplicative.toAdd hx
  · exact hl x

private theorem marked_complement_of_automizer (P : ReturningPair D)
    (hclass : OneInvolutionClass G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (f : A.normalizerMonoidHom.range ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ n x, a (n • x) = naturalAction (f n) (a x)) :
    ∃ (C : Subgroup (normalizer (A : Set G))) (l : C ≃* LinearGroup)
      (j : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' C ∧
      (∀ (c : C) (x : A),
        a (A.normalizerMonoidHom c x) = naturalAction (l c) (a x)) ∧
      FieldEmbedding A C a j := by
  obtain ⟨C,k,hC,_,hk⟩ := P.plane_normalizer_marked_complement hclass A hA hAR
  have ha' (c : C) (x : A) :
      a (A.normalizerMonoidHom c x) = naturalAction (k.trans f c) (a x) := by
    have hh := ha (k c) x
    change a ((k c : MulAut A) x) = _ at hh
    rwa [hk] at hh
  obtain ⟨j,hj⟩ := field_embedding_of_complement A C (k.trans f) a hC ha'
  exact ⟨C,k.trans f,j,hC,ha',hj⟩



private theorem field_commutes_base (c : Multiplicative Representation.SL2FourNatural.F) :
    Sporadic.Janko3.SourceRecognition.SingerField.fieldElement * baseRoot c =
      baseRoot c * Sporadic.Janko3.SourceRecognition.SingerField.fieldElement := by
  open Sporadic.Janko3.SourceRecognition.SingerField in
    have hh := fieldElement_conjugation
      (Multiplicative.ofAdd (algebraMap Representation.SL2FourNatural.F K c.toAdd))
  have hfour : ∀ c : Representation.SL2FourNatural.F, c ^ 4 = c := by decide +kernel
  have hp : (algebraMap Representation.SL2FourNatural.F
      Sporadic.Janko3.SourceRecognition.SingerField.K c.toAdd) ^ 4 =
      algebraMap Representation.SL2FourNatural.F
        Sporadic.Janko3.SourceRecognition.SingerField.K c.toAdd :=
    ((algebraMap Representation.SL2FourNatural.F
      Sporadic.Janko3.SourceRecognition.SingerField.K).map_pow c.toAdd 4).symm.trans
        (congrArg (algebraMap Representation.SL2FourNatural.F
          Sporadic.Janko3.SourceRecognition.SingerField.K) (hfour c.toAdd))
  change Sporadic.Janko3.SourceRecognition.SingerField.fieldElement * baseRoot c *
      Sporadic.Janko3.SourceRecognition.SingerField.fieldElement⁻¹ =
    Sporadic.Janko3.SourceRecognition.SingerField.root (Multiplicative.ofAdd
      ((algebraMap Representation.SL2FourNatural.F
        Sporadic.Janko3.SourceRecognition.SingerField.K c.toAdd) ^ 4)) at hh
  rw [hp] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

private theorem involution_mem_root (P : ReturningPair D) (s : G)
    (hs : s ^ 2 = 1) (hc : s ∈ centralizer (P.E : Set G)) : s ∈ P.R := by
  let C := centralizer (P.E : Set G)
  let Q := P.R.subgroupOf C
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer P.R_le_centralizer_E).mpr
    (LocalSixteen.Geometry.centralizer_E_le_normalizer_R P)
  have hQ : Nat.card Q = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe P.R_le_centralizer_E).toEquiv).trans P.R_card
  have hi : Q.index = 3 := by
    have hh := Q.card_mul_index
    rw [hQ,P.centralizer_E_card] at hh
    omega
  have hp := Q.pow_index_mem (⟨s,hc⟩ : C)
  rw [hi] at hp
  change s ^ 3 ∈ P.R at hp
  simpa only [pow_succ,hs,one_mul] using hp

private theorem field_position (P : ReturningPair D)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (hj : FieldEmbedding A C a j) (hE : (j.comp baseRoot).range = P.E) :
    j Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.R ∧
      j Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ A := by
  open Sporadic.Janko3.SourceRecognition.SingerField in
    let s := j fieldElement
  obtain ⟨_,_,_,_,_,hfield,horder,_,_⟩ := hj
  have hs : s ^ 2 = 1 := horder ▸ pow_orderOf_eq_one s
  have hc : s ∈ centralizer (P.E : Set G) := by
    intro x hx
    rw [← hE] at hx
    obtain ⟨c,rfl⟩ := hx
    have hh : s * j (baseRoot c) = j (baseRoot c) * s := by
      simpa only [map_mul] using congrArg j (field_commutes_base c)
    exact hh.symm
  refine ⟨involution_mem_root P s hs hc,?_⟩
  intro hA
  obtain ⟨c,hc,he⟩ := hfield
  have hcA : c ∈ A.subgroupOf (normalizer (A : Set G)) := by
    change (c : G) ∈ A
    change (c : G) = s at he
    exact he.symm ▸ hA
  have hc1 : c = 1 := mem_bot.mp (hC.disjoint.le_bot ⟨hcA,hc⟩)
  have hs1 : s = 1 := he.symm.trans (congrArg (fun x : normalizer (A : Set G) => (x : G)) hc1)
  simp [show j Sporadic.Janko3.SourceRecognition.SingerField.fieldElement = 1 from hs1] at horder

/-- Every square-one element of the actual root group belongs to one of its two planes. -/
theorem root_involution_in_planes (P : ReturningPair D)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) (s : G)
    (hR : s ∈ P.R) (hs : s ^ 2 = 1) : s ∈ P.A₁ eR ∨ s ∈ P.A₂ eR := by
  let r : P.R := ⟨s,hR⟩
  have he : (eR r) ^ 2 = 1 := by
    rw [← map_pow]
    exact (congrArg eR (show r ^ 2 = 1 from Subtype.ext hs)).trans eR.map_one
  rcases mul_eq_zero.mp
      ((Theory.GroupTheory.HyperbolicRecognition.root_square_eq_one (eR r)).mp he) with hx | hy
  · right
    change s ∈ (Theory.GroupTheory.HyperbolicRecognition.transportedPlane₂ eR).map P.R.subtype
    exact ⟨r,(Theory.GroupTheory.HyperbolicRecognition.mem_transportedPlane₂ eR r).mpr hx,rfl⟩
  · left
    change s ∈ (Theory.GroupTheory.HyperbolicRecognition.transportedPlane₁ eR).map P.R.subtype
    exact ⟨r,(Theory.GroupTheory.HyperbolicRecognition.mem_transportedPlane₁ eR r).mpr hy,rfl⟩

/-- Literal field embeddings in compatible plane markings share their base roots,
and their fourth-power involutions cross to the other plane. This applies to
prescribed complements, so a common overlap complement can be retained. -/
theorem field_overlap_of_markings (P : ReturningPair D)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root)
    (C₁ : Subgroup (normalizer (P.A₁ eR : Set G)))
    (a₁ : P.A₁ eR ≃* Plane)
    (j₁ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G)
    (C₂ : Subgroup (normalizer (P.A₂ eR : Set G)))
    (a₂ : P.A₂ eR ≃* Plane)
    (j₂ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G)
    (hC₁ : ((P.A₁ eR).subgroupOf (normalizer (P.A₁ eR : Set G))).IsComplement' C₁)
    (hj₁ : FieldEmbedding (P.A₁ eR) C₁ a₁ j₁)
    (hC₂ : ((P.A₂ eR).subgroupOf (normalizer (P.A₂ eR : Set G))).IsComplement' C₂)
    (hj₂ : FieldEmbedding (P.A₂ eR) C₂ a₂ j₂)
    (heq : ∀ (x : G) (hx₁ : x ∈ P.A₁ eR) (hx₂ : x ∈ P.A₂ eR),
      a₁ ⟨x,hx₁⟩ = a₂ ⟨x,hx₂⟩)
    (hl : ∀ x : P.E,
      (a₁ ⟨x,((P.planes_inf eR).ge.trans inf_le_left) x.property⟩).toAdd 1 = 0) :
    j₁.comp baseRoot = j₂.comp baseRoot ∧ (j₁.comp baseRoot).range = P.E ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₂ eR ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₂ eR := by
  have hE₁ : P.E ≤ P.A₁ eR := (P.planes_inf eR).ge.trans inf_le_left
  have hE₂ : P.E ≤ P.A₂ eR := (P.planes_inf eR).ge.trans inf_le_right
  have hroot₁ (c : Multiplicative Representation.SL2FourNatural.F) :
      j₁ (baseRoot c) = (a₁.symm (axis c) : G) := by
    change j₁ (Sporadic.Janko3.SourceRecognition.SingerField.root _) = _
    rw [hj₁.2.2.2.1]
    exact congrArg (fun v : Plane => (a₁.symm v : G)) (rootCoordinates_base c)
  have hroot₂ (c : Multiplicative Representation.SL2FourNatural.F) :
      j₂ (baseRoot c) = (a₂.symm (axis c) : G) := by
    change j₂ (Sporadic.Janko3.SourceRecognition.SingerField.root _) = _
    rw [hj₂.2.2.2.1]
    exact congrArg (fun v : Plane => (a₂.symm v : G)) (rootCoordinates_base c)
  have hs := center_axis_surjective P _ hE₁ a₁ hl
  have hsame : j₁.comp baseRoot = j₂.comp baseRoot := by
    apply MonoidHom.ext
    intro c
    obtain ⟨x,hx⟩ := hs c
    have hx₂ : a₂ (inclusion hE₂ x) = axis c :=
      (heq x (hE₁ x.property) (hE₂ x.property)).symm.trans hx
    change j₁ (baseRoot c) = j₂ (baseRoot c)
    rw [hroot₁,hroot₂,← hx,a₁.symm_apply_apply]
    rw [hx,← hx₂,a₂.symm_apply_apply]
    rfl
  have hE : (j₁.comp baseRoot).range = P.E := by
    apply le_antisymm
    · rintro _ ⟨c,rfl⟩
      change j₁ (baseRoot c) ∈ P.E
      obtain ⟨x,hx⟩ := hs c
      rw [hroot₁,← hx,a₁.symm_apply_apply]
      exact x.property
    · intro x hx
      let c := Multiplicative.ofAdd ((a₁ (inclusion hE₁ ⟨x,hx⟩)).toAdd 0)
      refine ⟨c,?_⟩
      change j₁ (baseRoot c) = x
      rw [hroot₁]
      have hh : a₁ (inclusion hE₁ ⟨x,hx⟩) = axis c := by
        change (a₁ (inclusion hE₁ ⟨x,hx⟩)).toAdd = ![_,0]
        funext i
        fin_cases i
        · rfl
        · exact hl ⟨x,hx⟩
      rw [← hh,a₁.symm_apply_apply]
      rfl

  have hp₁ := field_position P _ C₁ a₁ j₁ hC₁ hj₁ hE
  have hp₂ := field_position P _ C₂ a₂ j₂ hC₂ hj₂ (hsame ▸ hE)
  have ht₁ : (j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement) ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one (j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement)
    rwa [hj₁.2.2.2.2.2.2.1] at hh
  have ht₂ : (j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement) ^ 2 = 1 := by
    have hh := pow_orderOf_eq_one (j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement)
    rwa [hj₂.2.2.2.2.2.2.1] at hh
  have hs₁ := root_involution_in_planes P eR _ hp₁.1 ht₁
  have hs₂ := root_involution_in_planes P eR _ hp₂.1 ht₂
  exact ⟨hsame,hE,hs₁.resolve_left hp₁.2,hp₁.2,hs₂.resolve_right hp₂.2,hp₂.2⟩

/-- The actual field-affine subgroups have identical base-field translations,
parametrizing precisely the original common four-group. Every marking and
embedding is constructed from the original H-type seed and one-class input. -/
theorem compatible_field_embeddings (P : ReturningPair D) (hclass : OneInvolutionClass G)
    (eR : P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :
    ∃ (C₁ : Subgroup (normalizer (P.A₁ eR : Set G)))
      (f₁ : C₁ ≃* LinearGroup) (a₁ : P.A₁ eR ≃* Plane)
      (j₁ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G)
      (C₂ : Subgroup (normalizer (P.A₂ eR : Set G)))
      (f₂ : C₂ ≃* LinearGroup) (a₂ : P.A₂ eR ≃* Plane)
      (j₂ : Sporadic.Janko3.SourceRecognition.SingerField.Model →* G),
      ((P.A₁ eR).subgroupOf (normalizer (P.A₁ eR : Set G))).IsComplement' C₁ ∧
      (∀ (c : C₁) (x : P.A₁ eR),
        a₁ ((P.A₁ eR).normalizerMonoidHom c x) = naturalAction (f₁ c) (a₁ x)) ∧
      FieldEmbedding (P.A₁ eR) C₁ a₁ j₁ ∧
      ((P.A₂ eR).subgroupOf (normalizer (P.A₂ eR : Set G))).IsComplement' C₂ ∧
      (∀ (c : C₂) (x : P.A₂ eR),
        a₂ ((P.A₂ eR).normalizerMonoidHom c x) = naturalAction (f₂ c) (a₂ x)) ∧
      FieldEmbedding (P.A₂ eR) C₂ a₂ j₂ ∧
      (∀ (x : G) (hx₁ : x ∈ P.A₁ eR) (hx₂ : x ∈ P.A₂ eR),
        a₁ ⟨x,hx₁⟩ = a₂ ⟨x,hx₂⟩) ∧
      j₁.comp baseRoot = j₂.comp baseRoot ∧ (j₁.comp baseRoot).range = P.E ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₂ eR ∧
      j₁ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∈ P.A₁ eR ∧
      j₂ Sporadic.Janko3.SourceRecognition.SingerField.fieldElement ∉ P.A₂ eR := by
  obtain ⟨k₁,a₁,k₂,a₂,ha₁,ha₂,heq,_,hl⟩ := compatible_automizer_markings P hclass eR
  obtain ⟨C₁,f₁,j₁,hC₁,hf₁,hj₁⟩ := marked_complement_of_automizer P hclass _
    (P.A₁_card eR) (P.A₁_le_R eR) k₁ a₁ ha₁
  obtain ⟨C₂,f₂,j₂,hC₂,hf₂,hj₂⟩ := marked_complement_of_automizer P hclass _
    (P.A₂_card eR) (P.A₂_le_R eR) k₂ a₂ ha₂
  exact ⟨C₁,f₁,a₁,j₁,C₂,f₂,a₂,j₂,hC₁,hf₁,hj₁,hC₂,hf₂,hj₂,heq,
    field_overlap_of_markings P eR C₁ a₁ j₁ C₂ a₂ j₂ hC₁ hj₁ hC₂ hj₂ heq hl⟩

end CFSG.Quasithin.Janko23.J3Recognition.Ambient
