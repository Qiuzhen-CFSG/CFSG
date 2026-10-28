module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedCore
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions
public import Theory.GroupTheory.OddImageElementaryResidual
/-!
# Cubic displacement on the original exchanged Borel torus

The original C_L(z) has two-residual L₁ with intrinsic quotient E₉.
Consequently every odd-order image of any subgroup of C_L(z) has exponent
three. If B lies in M and fixes z, a displacement of B by s ∈ T ∩ L
lies in C_L(z): B normalizes L, and s normalizes B.

Apply this to the constructed Borel B = K₀ ∩ M and its literal map to
both cyclic torus factors. Every displacement by the original T ∩ L has
cube one. The map has kernel O₂(B), and the image of the original L₁
has order nine. The moving conjugation, prescribed Sylow intersection,
full quotient kernels and both component models are retained when the
result is applied to the original reduced actor K₀L₁T.

The semilinear action and its nontriviality still have to force field
order four. The remaining component/module exclusions and the universal
NaturalReduction are not conclusions of this module.
Source: Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
open Chapter13.Section08.Components.Swapped.LinearTwo
/-- The actual paired Borel torus, retaining the moving component, original
Sylow intersection, full two-core kernel, marked nine-group, and the
conjugation displacement by T ∩ L. This data is constructed below. -/
@[expose] def ExchangedTorusAction {G : Type*} [Group G] [Finite G]
    (H K X T L M : Subgroup G) (n : ℕ) (hn2 : 2 ≤ n) : Prop :=
    ∃ (t : G) (ht : t ∈ T) (hTH : T ≤ H),
      t ∉ normalizer (K : Set G) ∧
      ∃ (hOH : conjugateSpanBy K T ≤ H)
      (e : Chapter13.Section08.Source.starImage H (conjugateSpanBy K T) ≃*
        Chapter13.Section08.Source.starImage H K × Chapter13.Section08.Source.starImage H K)
      (P : Sylow 2 (Chapter13.Section08.Source.starImage H (conjugateSpanBy K T)))
      (hmstar : ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage H K) 2 (2 ^ n)),
      let O := conjugateSpanBy K T
      let B := SourceTorus.chosenLift H O hOH P
      let C := SourceActions.CommonTorus H O e P
      let f := SourceTorus.toCommonTori H O hOH e P hn2 hmstar
      ∃ hnB : T ≤ normalizer (B : Set G),
        (∀ a b, (e.symm (a,b) : H ⧸ pCore 2 H) = (a : H ⧸ pCore 2 H) *
          (QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩ * b *
            (QuotientGroup.mk' (pCore 2 H) ⟨t,hTH ht⟩)⁻¹)) ∧
        (P : Subgroup (Chapter13.Section08.Source.starImage H O)).map
          (Chapter13.Section08.Source.starImage H O).subtype =
            Chapter13.Section08.Source.starImage H (T ⊓ O) ∧
        B = O ⊓ M ∧ H ⊓ M = B ⊔ T ∧
        X ≤ B ∧ Even n ∧
        f.ker = pCore 2 B ∧ Function.Surjective f ∧
        Nat.card (X.subgroupOf B |>.map f) = 9 ∧
        ∀ (s : (T ⊓ L : Subgroup G)) (c : C × C),
          (SourceTorus.normalizerAction H O hOH e P hn2 hmstar
            ⟨s.val,hnB s.property.1⟩ c * c⁻¹) ^ 3 = 1

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))

include hz hTz in
/-- The actual point stabilizer has only cubic odd-order subgroup images.
Both the residual quotient and its intrinsic two-core are retained. -/
theorem SourceHypothesis.original_point_odd_image_cube
    {Q : Type*} [Group Q] (Y : Subgroup G)
    (hY : Y ≤ L ⊓ (D.fullSetup hZ T z).Gz) (f : Y →* Q)
    (ho : Odd (Nat.card Q)) (y : Y) : f y ^ 3 = 1 := by
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  let a : pResidual 2 C ≃* E.L₁ :=
    (pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective
  obtain ⟨_,_,_,e9,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e9
  have hc (x : pResidual 2 C ⧸ pCore 2 (pResidual 2 C)) : x ^ 3 = 1 := by
    apply e.injective
    rw [map_pow,map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3
        BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9) _
  let b := subgroupOfEquivOfLe hY
  have h := odd_image_cube_of_residual_quotient hc (Y.subgroupOf C)
    (f.comp b.toMonoidHom) ho (b.symm y)
  simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,b.apply_symm_apply] using h

include hz hTz in
/-- Actual displacement by T ∩ L has cube one in any odd-order image of
this point-fixing subgroup of M. Only the stated relative normalizations are used. -/
theorem SourceHypothesis.original_point_normalizer_odd_displacement_cube
    {Q : Type*} [Group Q] (B : Subgroup G)
    (hBM : B ≤ M L) (hBz : B ≤ (D.fullSetup hZ T z).Gz)
    (hnB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (f : B →* Q) (ho : Odd (Nat.card Q)) (s : ((T : Subgroup G) ⊓ L : Subgroup G)) (b : B) :
    (f (B.normalizerMonoidHom ⟨s.val,hnB s.property.1⟩ b) * (f b)⁻¹) ^ 3 = 1 := by
  let c : B := B.normalizerMonoidHom ⟨s.val,hnB s.property.1⟩ b * b⁻¹
  have hcL : (c : G) ∈ L :=
    le_normalizer_iff_commutator_le_left.mp hBM
      (commutator_mem_commutator s.property.2 b.property)
  let Y := B ⊓ L
  let y : Y := ⟨c.val,c.property,hcL⟩
  have hY : Y ≤ L ⊓ (D.fullSetup hZ T z).Gz :=
    le_inf inf_le_right (inf_le_left.trans hBz)
  have h := S.original_point_odd_image_cube D hZ z hz hTz Y hY
    (f.comp (inclusion inf_le_left)) ho y
  change f c ^ 3 = 1 at h
  simpa only [c,map_mul,map_inv] using h

variable (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTz hTV hbound hTI hns hH hKH hK hgen in
/-- Construct the original torus action and its cubic displacement bound,
including the marked component exchange and full Sylow intersection. -/
theorem SourceHypothesis.original_abelian_exchanged_torus_action
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    ExchangedTorusAction H K (D.fullSetup hZ T z).L₁ T L (M L) n hn2 := by
  obtain ⟨t,ht,hTH,htn,hOH,e,P,he,hP,hstar,hsol,hLB,hBM,hnB,heven,hBrank,hOT,hBeq,hMeq⟩ :=
    S.original_abelian_exchanged_borel D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hn2 hm
  change Chapter13.Section08.Source.starImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
    Chapter13.Section08.Source.starImage H K × Chapter13.Section08.Source.starImage H K at e
  change Sylow 2 (Chapter13.Section08.Source.starImage H (conjugateSpanBy K (T : Subgroup G))) at P
  let O := conjugateSpanBy K (T : Subgroup G)
  let B := SourceTorus.chosenLift H O hOH P
  have hmstar := hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm
  let f := SourceTorus.toCommonTori H O hOH e P hn2 hmstar
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := le_sup_right.trans hnB
  have hc : Nat.card ((D.fullSetup hZ T z).L₁.subgroupOf B |>.map f) = 9 := by
    have h := SourceActions.Markings.image_card B (D.fullSetup hZ T z).L₁ hLB f
      (by change IsPGroup 2 (SourceTorus.toCommonTori H O hOH e P hn2 hmstar).ker
          rw [SourceTorus.toCommonTori_ker]; exact pCore_isPGroup)
      (SourceActions.commonTori_odd H O e P hn2 hmstar)
    obtain ⟨_,_,_,e9,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
    exact h.trans ((Nat.card_congr e9.toEquiv).trans
      BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card)
  refine ⟨t,ht,hTH,htn,hOH,e,P,hmstar,hTB,he,hP,hBeq,hMeq,hLB,heven,
    SourceTorus.toCommonTori_ker H O hOH e P hn2 hmstar,
    SourceTorus.toCommonTori_surjective H O hOH e P hn2 hmstar,hc,?_⟩
  intro s c
  obtain ⟨b,rfl⟩ := SourceTorus.toCommonTori_surjective H O hOH e P hn2 hmstar c
  rw [SourceTorus.normalizerAction_toCommonTori]
  exact S.original_point_normalizer_odd_displacement_cube D hZ z hz hTz B hBM
    ((borelLift_le H O hOH _).trans (hOH.trans hH.2.1)) hTB f
    (SourceActions.commonTori_odd H O e P hn2 hmstar) s b

include hz hTV hTz hbound hTI hns hH in
/-- The original reduced actor retains the full even-field, Borel and core
conclusions, together with the actual cubic displacement on its paired torus. -/
theorem SourceHypothesis.original_abelian_reduced_torus_actions :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (K.subgroupOf J).IsCComponent ∧
      (((K.subgroupOf J).Normal ∧
          AbelianLieHigherFieldModel (K ⧸ pCore 2 K) ∧
          AbelianLieHigherFieldModel (Chapter13.Section08.Source.starImage J K)) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          ∃ (n : ℕ) (hn2 : 2 ≤ n), Even n ∧
            ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n) ∧
            ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage J K) 2 (2 ^ n) ∧
            (primeToResidual 3 J).map J.subtype = K₀ ∧
            (D.fullSetup hZ T z).L₁ ≤ K₀ ⊓ M L ∧
            K₀ ⊔ (T : Subgroup G) = J ∧
            J ⊓ M L = (K₀ ⊓ M L) ⊔ (T : Subgroup G) ∧
            Group.IsSolvable (K₀ ⊓ M L : Subgroup G) ∧
            primeRank 3 (K₀ ⊓ M L : Subgroup G) = 2 ∧
            (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
              normalizer ((K₀ ⊓ M L : Subgroup G) : Set G) ∧
            (T : Subgroup G) ⊓ K₀ ≤ (D.fullSetup hZ T z).R₁ ∧
            ExchangedTorusAction J K (D.fullSetup hZ T z).L₁ T L (M L) n hn2)) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,halt⟩ :=
    S.original_abelian_reduced_even_Lie_models_core D hZ z hz hTV hTz hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with hnormal | ⟨hn,hi,n,hn2,heven,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB,hcore⟩
  · exact Or.inl hnormal
  · exact Or.inr ⟨hn,hi,n,hn2,heven,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB,hcore,
      S.original_abelian_exchanged_torus_action D hZ z hz hTz hTV hbound hTI hns
        hJ hKle hKJ rfl hn hn2 hm⟩


end CFSG.Quasithin.Chapter12.Section06
