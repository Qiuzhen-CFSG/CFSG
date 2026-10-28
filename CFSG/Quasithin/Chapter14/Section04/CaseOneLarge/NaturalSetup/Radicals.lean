module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Frame
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations

/-!
# The two original radical images in the natural frame

G.2.5 gives [V,U]=V₁, pointwise fixation of V₁ and an image of order four.
For any natural frame with ordered points (V₁ᵍ,V₁,V₁ˡ), these action identities
put the literal images of U and Uᵍ in the second and first coordinate radicals.
Comparison with the original star map, using their identical centralizer
kernels, gives order four without changing the frame's actor or quotient.
Right conjugation preserves that order. Thus both containments are equalities.

The final theorem applies the existing source Sylow construction with these
images, the proved kernel normalization, and the same l in the ordered kernel
product. The original product Uᵍ C_U(V₂) C_{Uˡ}(V) is therefore Sylow in LS.

Source: Aschbacher--Smith, G.2.5(1--3) and 14.4.7, printed pp.335--336,1009;
refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Module
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension.RankCore.GaschutzComplement
open Matrix.PSL3Two
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

set_option maxRecDepth 10000 in
private theorem secondRadical_entries : ∀ a : SL, a ∈ SourceFlag.secondRadical ↔
    a.val 0 0 = 1 ∧ a.val 0 1 = 0 ∧ a.val 0 2 = 0 ∧
    a.val 1 1 = 1 ∧ a.val 2 0 = 0 ∧ a.val 2 1 = 0 ∧ a.val 2 2 = 1 := by
  decide +kernel

private theorem pointV_of_action (a : SL)
    (hf : a.val.mulVec ![1,0,0] = ![1,0,0])
    (hd : ∀ v : Fin 3 → ZMod 2, (a.val.mulVec v - v) 1 = 0 ∧
      (a.val.mulVec v - v) 2 = 0) : a ∈ MarkedAutomorphisms.pointV := by
  have hf0 := congrFun hf 0
  have hf1 := congrFun hf 1
  have hf2 := congrFun hf 2
  have hd1 := hd ![0,1,0]
  have hd2 := hd ![0,0,1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hf0 hf1 hf2 hd1 hd2
  exact ⟨hf0,hf1,hf2,sub_eq_zero.mp hd1.1,hd2.1,hd1.2,sub_eq_zero.mp hd2.2⟩

private theorem secondRadical_of_action (a : SL)
    (hf : a.val.mulVec ![0,1,0] = ![0,1,0])
    (hd : ∀ v : Fin 3 → ZMod 2, (a.val.mulVec v - v) 0 = 0 ∧
      (a.val.mulVec v - v) 2 = 0) : a ∈ SourceFlag.secondRadical := by
  have hf0 := congrFun hf 0
  have hf1 := congrFun hf 1
  have hf2 := congrFun hf 2
  have hd0 := hd ![1,0,0]
  have hd2 := hd ![0,0,1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hf0 hf1 hf2 hd0 hd2
  exact (secondRadical_entries a).mpr ⟨sub_eq_zero.mp hd0.1,hf0,hd2.1,hf1,hd0.2,hf2,sub_eq_zero.mp hd2.2⟩

omit [Finite G] in
private theorem action_displacement {I : Subgroup G} {hIV : I ≤ normalizer (V : Set G)}
    (m : SourceNaturalAction I V hIV) (A P : Subgroup G)
    (hmove : ⁅A,V⁆ ≤ P) (x : I) (hx : (x : G) ∈ A) (v : V) :
    ((V.normalizerMonoidHom (inclusion hIV x) v * v⁻¹ : V) : G) ∈ P ∧
    (m.space (V.normalizerMonoidHom (inclusion hIV x) v * v⁻¹)).toAdd =
      (m.actor x).val.mulVec (m.space v).toAdd - (m.space v).toAdd := by
  refine ⟨hmove (commutator_mem_commutator hx v.property), ?_⟩
  rw [map_mul,map_inv,toAdd_mul,toAdd_inv,m.intertwines,sub_eq_add_neg]

omit [Finite G] in
private theorem map_rightConjugate {I U : Subgroup G} (hUI : U ≤ I)
    (g : I) {K : Type*} [Group K] (f : I →* K) :
    ((rightConjugate U g).subgroupOf I).map f =
      ((U.subgroupOf I).map f).map (MulAut.conj (f g)⁻¹).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x,⟨u,hu,he⟩,rfl⟩
    let uI : I := ⟨u,hUI hu⟩
    have he' : x = g⁻¹ * uI * g := Subtype.ext (by simpa using he.symm)
    refine ⟨f uI,mem_map_of_mem f hu,?_⟩
    simp [he',map_mul,map_inv]
  · rintro ⟨a,⟨u,hu,rfl⟩,rfl⟩
    refine ⟨g⁻¹ * u * g,?_,?_⟩
    · exact ⟨u,hu,by simp⟩
    · simp [map_mul,map_inv]

/-- The full original radical has order four in every natural marking.
The comparison uses the same centralizer kernel as the literal star map. -/
theorem source_radical_card (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {hIV : conjugateSpan F.U L ≤ normalizer (V : Set G)}
    (m : SourceNaturalAction (conjugateSpan F.U L) V hIV) :
    Nat.card ((F.U.subgroupOf (conjugateSpan F.U L)).map m.actor) = 4 := by
  obtain ⟨l,_,_,_,⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives F hne g hg hgP hgH
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  let D := sourceSetup F L
  let I := conjugateSpan F.U L
  have hILT : I ≤ D.LT := by
    rw [show I = L ⊔ F.U from source_span_eq d earlier hq chosen structural alternatives F hne g hg hgP hgH]
    exact sup_le le_sup_left (hUT.trans le_sup_right)
  let q : I →* D.Star := (QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion hILT)
  have hk : q.ker = m.actor.ker := by
    rw [m.ker_eq]
    ext x
    change QuotientGroup.mk' (pCore 2 D.LT) (inclusion hILT x) = 1 ↔
      (x : G) ∈ centralizer (V : Set G)
    rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact chosen.core_centralizes (mem_map_of_mem D.LT.subtype hx)
    · intro hx
      have hm := (higherRankHypothesis d earlier hq chosen).centralizer_LT structural ▸
        (show (x : G) ∈ (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) from ⟨hILT x.property,hx⟩)
      obtain ⟨y,hy,he⟩ := hm
      exact (show y = inclusion hILT x from Subtype.ext he) ▸ hy
  have hmap : (F.U.subgroupOf I).map q = D.star D.U := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨inclusion hILT x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,le_conjugateSpan F.U L hx⟩,hx,rfl⟩
  calc
    Nat.card ((F.U.subgroupOf I).map m.actor) = Nat.card ((F.U.subgroupOf I).map q) := by
      rw [← relIndex_ker,← relIndex_ker,hk]
    _ = 4 := by rw [hmap,B.card_star_U hUT hphi]; norm_num

/-- The two literal source radical images in the existing ordered frame.
No replacement of its quotient map or choice of third transporter is made. -/
theorem source_radical_images (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) {hIV : conjugateSpan F.U L ≤ normalizer (V : Set G)}
    (m : SourceNaturalFrame F.U V (F.Vi 1) (F.Vi 2) L g l hIV) :
    (F.U.subgroupOf (conjugateSpan F.U L)).map m.actor = SourceFlag.secondRadical ∧
    ((rightConjugate F.U g).subgroupOf (conjugateSpan F.U L)).map m.actor =
      MarkedAutomorphisms.pointV := by
  obtain ⟨l',_,_,_,⟨B⟩⟩ := source_almostSpecial d earlier hq chosen structural alternatives F hne g hg hgP hgH
  have hUT := source_closure_le_sylow d earlier hq chosen structural alternatives F
  have hphi := source_frattini d earlier hq chosen structural alternatives F hne
  have hmove : ⁅F.U,V⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (B.commutator_V_U_eq_point hUT hphi).le
  have hfix : F.U ≤ centralizer (F.Vi 1 : Set G) := B.setup.U_le_centralizer_point
  have hmoveg : ⁅rightConjugate F.U g,V⁆ ≤ rightConjugate (F.Vi 1) g := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hmove
    rw [map_commutator] at hh
    have hv : V.map (MulAut.conj g⁻¹).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (V : Set G)).inv_mem (chosen.normalizes hg))
    rwa [hv] at hh
  have hfixg : rightConjugate F.U g ≤ centralizer (rightConjugate (F.Vi 1) g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hfix
    rwa [LargerDimension.RankCore.CentralizerGeometry.centralizer_map] at hh
  have hle : (F.U.subgroupOf (conjugateSpan F.U L)).map m.actor ≤ SourceFlag.secondRadical := by
    rintro _ ⟨x,hx,rfl⟩
    apply secondRadical_of_action
    · obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd ![0,1,0])
      have hvl : (v : G) ∈ F.Vi 1 := (m.line_one v).mpr (by simp [hv])
      have he := (m.toSourceNaturalAction.fixes_iff x v).mpr (hfix hx _ hvl)
      simpa [hv] using he
    · intro w
      obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd w)
      obtain ⟨hp,he⟩ := action_displacement m.toSourceNaturalAction F.U (F.Vi 1) hmove x hx v
      have hh := (m.line_one _).mp hp
      simpa only [he,hv,toAdd_ofAdd] using hh
  have hleg : ((rightConjugate F.U g).subgroupOf (conjugateSpan F.U L)).map m.actor ≤ MarkedAutomorphisms.pointV := by
    rintro _ ⟨x,hx,rfl⟩
    apply pointV_of_action
    · obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd ![1,0,0])
      have hvl : (v : G) ∈ rightConjugate (F.Vi 1) g := (m.line_g v).mpr (by simp [hv])
      have he := (m.toSourceNaturalAction.fixes_iff x v).mpr (hfixg hx _ hvl)
      simpa [hv] using he
    · intro w
      obtain ⟨v,hv⟩ := m.space.surjective (Multiplicative.ofAdd w)
      obtain ⟨hp,he⟩ := action_displacement m.toSourceNaturalAction _ _ hmoveg x hx v
      have hh := (m.line_g _).mp hp
      simpa only [he,hv,toAdd_ofAdd] using hh
  have hc := source_radical_card d earlier hq chosen structural alternatives F hne g hg hgP hgH m.toSourceNaturalAction
  have hc₂ : Nat.card SourceFlag.secondRadical = 4 := by
    rw [SourceFlag.secondRadical,MulEquiv.toMonoidHom_eq_coe,comap_equiv_eq_map_symm,card_map_of_injective (MulAut.conj (Bruhat.perm 2)).symm.injective]
    exact MarkedAutomorphisms.card_pointV
  have hLI : L ≤ conjugateSpan F.U L := by
    rw [source_span_eq d earlier hq chosen structural alternatives F hne g hg hgP hgH]
    exact le_sup_left
  have hcg : Nat.card (((rightConjugate F.U g).subgroupOf (conjugateSpan F.U L)).map m.actor) = 4 := by
    rw [map_rightConjugate (le_conjugateSpan F.U L) ⟨g,hLI hg⟩ m.actor,
      card_map_of_injective (MulAut.conj (m.actor ⟨g,hLI hg⟩)⁻¹).injective]
    exact hc
  exact ⟨eq_of_le_of_card_ge hle (by omega),
    eq_of_le_of_card_ge hleg (by rw [hcg,MarkedAutomorphisms.card_pointV])⟩
/-- The actual product displayed in 14.4.7 is Sylow in its required carrier.
This applies the existing Sylow construction with both radical premises proved. -/
theorem source_flag_sylow (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ l : G, l ∈ L ∧ l ∉ F.Li L 2 ⊔ (T : Subgroup G) ∧
      (candidateSylow F.U V (F.Vi 2) g l : Set G) =
        (rightConjugate F.U g : Set G) * (F.U ⊓ centralizer (F.Vi 2 : Set G) : Set G) *
          (rightConjugate F.U l ⊓ centralizer (V : Set G) : Set G) ∧
      ∃ P : Sylow 2 ↥(L ⊔ candidateSylow F.U V (F.Vi 2) g l),
        (P : Subgroup ↥(L ⊔ candidateSylow F.U V (F.Vi 2) g l)).map
          (L ⊔ candidateSylow F.U V (F.Vi 2) g l).subtype =
            candidateSylow F.U V (F.Vi 2) g l := by
  obtain ⟨l,hl,hlP,hIV,m,_,_,hcore,_⟩ :=
    source_natural_frame d earlier hq chosen structural alternatives F hne g hg hgP hgH
  obtain ⟨hU,hUg⟩ := source_radical_images d earlier hq chosen structural alternatives
    F hne g hg hgP hgH l m
  exact ⟨l,hl,hlP,source_sylow F.U V (F.Vi 1) (F.Vi 2) L g l hg hl hIV m
    (source_span_eq d earlier hq chosen structural alternatives F hne g hg hgP hgH)
    hU hUg (source_span_kernel d earlier hq chosen structural alternatives F hne g hg hgP hgH)
    (source_span_core_normalizes d earlier hq chosen structural alternatives F hne g hg hgP hgH) hcore⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup
