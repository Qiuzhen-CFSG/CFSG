module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ParabolicApplication
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.Representation.G2OrthogonalCover.QuadraticObstruction
public import Theory.GroupTheory.SylowCentralizerComplement

/-!
# The cubic-fixed order-four element in the original G₂ branch

Nonabelianness and the original Frattini bound identify Φ(U_H) with V₁.
Squaring therefore gives a nonzero invariant quadratic form on the literal
U_H/V₁. The marked natural quotient is a full G₂(2)′ cover. The quadratic
obstruction on its universal seven-space supplies a fixed quotient vector
with nonzero square. Its lift has order four. Averaging over a cubic subgroup
corrects the lift by V₁ to make it fixed, preserving that square.

The final theorem takes precisely the original natural setup and selected
G₂ row; it discharges Frattini, quadratic-form, and full-cover premises. Its
witness is the input of the original elementary second-layer contradiction.
Source: Aschbacher–Smith13.5.25, printed p.925, using13.5.21 andI.1.6(5).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.G2FixedFour
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  (h : D.Hypothesis) (hU : ¬IsMulCommutative D.UH)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

include h hU
omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The original point is exactly the Frattini subgroup of the nonabelian closure. -/
theorem frattini_eq_point : frattini D.UH = D.V₁.subgroupOf D.UH := by
  have hp : IsPGroup 2 D.UH := (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup)
  let : Fact (IsPGroup 2 D.UH) := ⟨hp⟩
  have hle : frattini D.UH ≤ D.V₁.subgroupOf D.UH :=
    fun x hx => h.frattini_UH_le_point (mem_map_of_mem D.UH.subtype hx)
  have hcard : Nat.card (D.V₁.subgroupOf D.UH) = 2 := by
    exact (Nat.card_congr (subgroupOfEquivOfLe (show D.V₁≤D.UH from
      h.point_lt.le.trans (le_conjugateSpanBy D.Vplus D.H))).toEquiv).trans h.point_card
  have hn : frattini D.UH ≠ ⊥ := by
    intro he
    apply hU
    apply (_root_.commutator_eq_bot_iff _).mp
    exact bot_unique (he ▸ commutator_le_frattini_of_isPGroup (p:=2))
  have hd : Nat.card (frattini D.UH) ∣ 2 := hcard ▸ card_dvd_of_le hle
  have hc : Nat.card (frattini D.UH) = 2 := (Nat.prime_two.eq_one_or_self_of_dvd _ hd).resolve_left
    (fun hh => hn (Subgroup.card_eq_one.mp hh))
  exact eq_of_le_of_card_ge hle (by rw [hc,hcard])

omit [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The literal Frattini subgroup has order two. -/
theorem frattini_card : Nat.card (frattini D.UH)=2 := by
  rw [frattini_eq_point h hU]
  exact (Nat.card_congr (subgroupOfEquivOfLe (show D.V₁≤D.UH from
    h.point_lt.le.trans (le_conjugateSpanBy D.Vplus D.H))).toEquiv).trans h.point_card

variable [Fact (IsPGroup 2 D.UH)]
local instance : IsElementaryAbelian 2 (D.UH ⧸ frattini D.UH) := isElementaryAbelian_quotient_frattini

/-- Identify the original point quotient with the actual Frattini quotient. -/
def frattiniCoordinates : Action.Space D ≃ₗ[ZMod 2] Additive (D.UH ⧸ frattini D.UH) :=
  let e := QuotientGroup.quotientMulEquivOfEq (frattini_eq_point h hU).symm
  LinearEquiv.ofBijective (e.toAdditive.toAddMonoidHom.toZModLinearMap 2)
    ⟨e.injective,e.surjective⟩

/-- The original quotient carries its literal squaring form. -/
def squareForm : QuadraticForm (ZMod 2) (Action.Space D) :=
  (SmallFrattini.quotientQuadraticForm (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup) (frattini_card h hU)).comp
    (frattiniCoordinates h hU).toLinearMap

/-- The form retains the square of each original group representative. -/
theorem squareForm_mk (u : D.UH) :
    squareForm h hU (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
      (SmallFrattini.binaryMark (frattini_card h hU)
        (SmallFrattini.quotientSquare (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup) (frattini_card h hU)
          (QuotientGroup.mk' (frattini D.UH) u))).toAdd := rfl

/-- A zero squaring form would make the whole closure elementary abelian. -/
theorem squareForm_ne_zero : squareForm h hU ≠ 0 := by
  intro he
  have hs (u : D.UH) : u^2=1 := by
    have hz := congrArg (fun q : QuadraticForm (ZMod 2) (Action.Space D) =>
      q (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u))) he
    rw [squareForm_mk] at hz
    have hi := (SmallFrattini.binaryMark (frattini_card h hU)).injective
      (show SmallFrattini.binaryMark (frattini_card h hU)
        (SmallFrattini.quotientSquare (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup) (frattini_card h hU)
          (QuotientGroup.mk' (frattini D.UH) u)) =
          SmallFrattini.binaryMark (frattini_card h hU) 1 from by
            rw [map_one]; exact congrArg Multiplicative.ofAdd hz)
    exact congrArg Subtype.val hi
  apply hU
  apply isMulCommutative_iff.mpr
  have hinv (x : D.UH) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
  intro x y
  calc
    x*y = (x*y)⁻¹ := (hinv _).symm
    _ = y*x := by rw [mul_inv_rev,hinv,hinv]

/-- Every original star action preserves the squaring form. -/
theorem squareForm_invariant (x : Hstar D.H) (u : Action.Space D) :
    squareForm h hU (Action.starRepresentation D h x u)=squareForm h hU u := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D.H) x
  obtain ⟨v,hv⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) u.toMul
  have heu : Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) v)=u := congrArg Additive.ofMul hv
  rw [←heu]
  rw [Action.starRepresentation_apply,squareForm_mk,squareForm_mk]
  let a : MulAut D.UH := D.UH.normalizerMonoidHom
    ⟨x.val,le_normalizer_conjugateSpanBy D.Vplus D.H x.property⟩
  have he := SmallFrattini.quotientSquare_invariant (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup)
    (frattini_card h hU) a (QuotientGroup.mk' (frattini D.UH) v)
  rw [Subgroup.quotientAut_apply_mk] at he
  exact congrArg (fun z => (SmallFrattini.binaryMark (frattini_card h hU) z).toAdd) he


/-- A nonzero square value gives an element of exact order four. -/
theorem order_four_of_squareForm_ne_zero (u : D.UH)
    (hu : squareForm h hU (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u))≠0) :
    orderOf u=4 := by
  let z := SmallFrattini.quotientSquare
    (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup) (frattini_card h hU)
    (QuotientGroup.mk' (frattini D.UH) u)
  have hz : (z:D.UH)=u^2 := SmallFrattini.quotientSquare_apply_mk _ _ u
  have hz2 : z^2=1 := frattini_card h hU ▸ (pow_card_eq_one' (x:=z))
  have h4 : u^4=1 := by
    have hh := congrArg Subtype.val hz2
    change (z:D.UH)^2=1 at hh
    rw [hz,←pow_mul] at hh
    exact hh
  have h2 : u^2≠1 := by
    intro hh
    apply hu
    rw [squareForm_mk]
    have he : z=1 := Subtype.ext (hz.trans hh)
    change (SmallFrattini.binaryMark (frattini_card h hU) z).toAdd=0
    rw [he,map_one]
    rfl
  exact orderOf_eq_prime_pow (p:=2) (n:=1) h2 h4

/-- The original squaring quotient gives an order-four lift fixed modulo its
point by the actual selected G₂ actor. -/
theorem exists_fixed_quotient_order_four (K : Subgroup G)
    (hn : (starImage D.H K).Normal)
    (hne : starImage D.H K ≠ ⊥)
    (hgen : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K)=⊤)
    (f : Catalogue.actor D K ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      fV (CentralQuotient.representation D h K hn b.val u)=
        g2DerivedNatural (ZMod 2) (f b) (fV u)) :
    ∃ u : D.UH, orderOf u=4 ∧
      squareForm h hU (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u))≠0 ∧
      ∀ b : Catalogue.actor D K,
      Action.starRepresentation D h b.val
        (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u))=
        Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) := by
  let := hn
  let N := starImage D.H K
  let A := Catalogue.actor D K
  let : IsSimpleGroup A := f.isSimpleGroup_congr.mpr Atlas.G2.isSimple_commutator_binary
  have hNA : N=A := by
    rcases (inferInstance : (N.subgroupOf A).Normal).eq_bot_or_eq_top with hb|ht
    · have he := congrArg (map A.subtype) hb
      rw [map_subgroupOf_eq_of_le (show N≤A from le_sup_left),Subgroup.map_bot] at he
      exact (hne he).elim
    · have he := congrArg (map A.subtype) ht
      rw [map_subgroupOf_eq_of_le (show N≤A from le_sup_left),←MonoidHom.range_eq_map,A.range_subtype] at he
      exact he
  let ρ : Representation (ZMod 2) (Hstar D.H) (Action.Space D) := Action.starRepresentation D h
  let σ : Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2))) (Action.Space D) :=
    ρ.comp (A.subtype.comp f.symm.toMonoidHom)
  let p : σ.IntertwiningMap (Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2)) := {
    toLinearMap := fV.toLinearMap.comp (CentralQuotient.projection D h K)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change fV (CentralQuotient.projection D h K
        (ρ (f.symm g).val v))= _
      rw [←CentralQuotient.representation_mk D h K hn,hfV,f.apply_symm_apply]
      rfl }
  have hp : OneCohomology.IsCover p := by
    refine ⟨fV.surjective.comp (CentralQuotient.centerSpace D h K).mkQ_surjective,?_,?_⟩
    · intro v hv g
      have hz : v∈CentralQuotient.centerSpace D h K := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact fV.injective (hv.trans fV.map_zero.symm)
      exact hz ⟨(f.symm g).val,hNA.ge (f.symm g).property⟩
    · apply top_unique
      rw [←hgen]
      apply Submodule.span_le.mpr
      rintro _ ⟨g,hg,v,_,rfl⟩
      have hh := Coinvariants.sub_mem_ker (ρ:=σ) (f ⟨g,hNA.le hg⟩) v
      change ρ (f.symm (f ⟨g,hNA.le hg⟩)).val v-v ∈ _ at hh
      rw [f.symm_apply_apply] at hh
      exact hh
  obtain ⟨w,hw,hq⟩ := Atlas.G2.Natural.OrthogonalCover.cover_exists_fixed_quadratic_ne_zero
    σ p hp (squareForm h hU) (fun g v => squareForm_invariant h hU _ v)
    (squareForm_ne_zero h hU)
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) w.toMul
  have heu : Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)=w := congrArg Additive.ofMul hu
  refine ⟨u,order_four_of_squareForm_ne_zero h hU u (heu ▸ hq),heu ▸ hq,?_⟩
  intro b
  have hh := hw (f b)
  change ρ (f.symm (f b)).val w=w at hh
  rw [f.symm_apply_apply,←heu] at hh
  exact hh

/-- A cubic subgroup has a fixed order-four representative in the original
point coset; the point correction does not change its square. -/
theorem exists_cubic_fixed_order_four (K : Subgroup G)
    (hn : (starImage D.H K).Normal) (hne : starImage D.H K ≠ ⊥)
    (hgen : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H K)=⊤)
    (f : Catalogue.actor D K ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      fV (CentralQuotient.representation D h K hn b.val u)=
        g2DerivedNatural (ZMod 2) (f b) (fV u))
    (A : Subgroup G) (hAK : A≤K) (hAH : A≤D.H) (hA : Nat.card A=3) :
    ∃ j : G, j∈D.UH ∧ orderOf j=4 ∧ j∈centralizer (A:Set G) := by
  obtain ⟨u,hu,huq,hfix⟩ := exists_fixed_quotient_order_four h hU K hn hne hgen f fV hfV
  have hAP : A≤normalizer (D.V₁:Set G) :=
    (hAH.trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _)
  have hdisp (a:G) (ha:a∈A) : ⁅a,(u:G)⁆∈D.V₁ := by
    let aH : D.H := ⟨a,hAH ha⟩
    let b : Catalogue.actor D K := ⟨QuotientGroup.mk' (pCore 2 D.H) aH,
      (show starImage D.H K≤Catalogue.actor D K from le_sup_left)
        (mem_map_of_mem _ (hAK ha))⟩
    have hh := hfix b
    rw [Action.starRepresentation_apply] at hh
    have hm := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective hh)
    simpa only [mem_subgroupOf,coe_div,coe_mul,coe_inv,div_eq_mul_inv,commutatorElement_def] using hm
  let P : Sylow 2 A := Sylow.nonempty.some
  have hP : (P:Subgroup A)=⊥ := by
    apply Subgroup.card_eq_one.mp
    apply P.isPGroup'.card_eq_or_dvd.resolve_right
    intro hd
    have hh : 2∣Nat.card A := hd.trans (card_subgroup_dvd_card (P:Subgroup A))
    rw [hA] at hh
    norm_num at hh
  have hp (v:G) (hv:v∈D.V₁) : v^2=1 := by
    have hh := (pow_card_eq_one' (x:=(⟨v,hv⟩:D.V₁)))
    rw [h.point_card] at hh
    exact congrArg Subtype.val hh
  let : IsMulCommutative D.V₁ := (isCyclic_of_prime_card h.point_card).isMulCommutative
  obtain ⟨v,hv,hfixed⟩ := fixed_coset_of_sylow A D.V₁ hAP hp P u.val hdisp (by
    intro a ha
    have he : a=1 := by
      change a∈(P:Subgroup A) at ha
      rw [hP] at ha
      exact mem_bot.mp ha
    rw [he]
    exact Commute.one_left _)
  have hvU : v∈D.UH := (h.point_lt.le.trans (le_conjugateSpanBy D.Vplus D.H)) hv
  let j : D.UH := ⟨v*u.val,D.UH.mul_mem hvU u.property⟩
  have hj : QuotientGroup.mk' (D.V₁.subgroupOf D.UH) j=
      QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u := by
    change QuotientGroup.mk' (D.V₁.subgroupOf D.UH) ((⟨v,hvU⟩:D.UH)*u)=_
    rw [map_mul,show QuotientGroup.mk' (D.V₁.subgroupOf D.UH) (⟨v,hvU⟩:D.UH)=1 from
      (QuotientGroup.eq_one_iff _).mpr hv,one_mul]
  refine ⟨j,j.property,?_,hfixed⟩
  change orderOf (D.UH.subtype j)=4
  rw [orderOf_injective D.UH.subtype D.UH.subtype_injective j]
  apply order_four_of_squareForm_ne_zero h hU j
  rw [hj]
  exact huq

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.G2FixedFour
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix

open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

include d h e in
/-- Original13.5.25 supplies the cubic-fixed element of order four in U_H.
The natural-cover geometry and original source hypotheses discharge every
quadratic and commutator-generation premise. -/
theorem g2_cubic_fixed_order_four (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus:Set G)≤M⊓normalizer (D.V:Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁≤K)
    (hn : (starImage D.H K).Normal)
    (f : Catalogue.actor D K ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      fV (CentralQuotient.representation D h K hn b.val u)=
        g2DerivedNatural (ZMod 2) (f b) (fV u))
    (A : Subgroup G) (hAL : A≤D.L₁) (hA : Nat.card A=3) :
    ∃ j : G, j∈D.UH ∧ orderOf j=4 ∧ j∈centralizer (A:Set G) := by
  let : Fact (IsPGroup 2 D.UH) := ⟨h.g2_hypothesis.U_isPGroup⟩
  have hi := NormalBranch.SourceOrthogonal.seed_index d
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke (selected_H_mem h)).stronglyQuasithin
  have hm := source_local_component_commutator d h e h1221 hc K s
  have hg := group_conclusions s h hSQ hi hU hLK (seed_identity d h) hm
    (selected_actor_normalization s h hi hU).2
  have hgen := linear_generation D h s hLK hg.1 (seed_identity d h)
  have hne : starImage D.H K≠⊥ := by
    intro he
    apply s.moved
    rw [he,commutator_bot_left]
  exact G2FixedFour.exists_cubic_fixed_order_four h hU K hn hne hgen f fV hfV A
    (hAL.trans hLK) (hAL.trans (hLK.trans s.le_H)) hA

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
