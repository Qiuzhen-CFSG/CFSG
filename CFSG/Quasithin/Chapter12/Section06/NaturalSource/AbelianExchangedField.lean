module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedTorus
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ExchangedTorusField
/-!
# The marked exchanged torus field restriction

The original cubic displacement is transported through the literal
binary Borel quotient. The ambient product action either preserves or
exchanges the two factors; the field calculation forces it to fix the
entire torus when n > 2. Pulling back through the original torus map puts
[T ∩ L,B] in the intrinsic O₂(B), with B = K₀ ∩ M.

The application retains the moving coordinates, Sylow intersection,
order-nine residual image, both component models and the full quotient
kernels on the original reduced actor K₀L₁T. The remaining nontriviality
of the original T ∩ L action must rule out the core-containment branch
before field order four is concluded. The other component/module
exclusions and universal NaturalReduction remain separate obligations.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter13.Section08.Components Chapter13.Section08.Components.Swapped
open Chapter13.Section08.Components.Swapped.LinearTwo
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

private theorem torus_action_eq_one_of_cube [IsQuasisimple Q]
    (H O : Subgroup G) (hOH : O ≤ H)
    (e : Chapter13.Section08.Source.starImage H O ≃* Q × Q)
    (P : Sylow 2 (Chapter13.Section08.Source.starImage H O))
    {n : ℕ} (hn : 2 < n) (hm : ClassicalGroup.IsPSL Q 2 (2^n))
    {g : G} (hgH : g ∈ H) (hgO : g ∈ normalizer (O : Set G))
    (hgB : g ∈ normalizer (SourceTorus.chosenLift H O hOH P : Set G))
    (hc : ∀ c, (SourceTorus.normalizerAction H O hOH e P (Nat.le_of_lt hn) hm
      ⟨g,hgB⟩ c * c⁻¹)^3 = 1) :
    SourceTorus.normalizerAction H O hOH e P (Nat.le_of_lt hn) hm ⟨g,hgB⟩ = 1 := by
  let S := SourceTorus.chosenSylow H O e P
  let a := SourceActions.productAction H O hOH e hgH hgO
  let b := SourceActions.binaryAction H O hOH e P hgH hgO hgB
  let f := SourceActions.binaryToCommon H O e P (Nat.le_of_lt hn) hm
  have hk : f.ker = pCore 2 (BinaryBorel.borel S) := by
    change ((SourceTorus.commonTorusCoordinates H O e P (Nat.le_of_lt hn) hm).toMonoidHom.comp
      (BinaryBorel.productMap S)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _
      (SourceTorus.commonTorusCoordinates H O e P (Nat.le_of_lt hn) hm).injective,
      BinaryBorel.productMap_ker]
  have he (x : BinaryBorel.borel S) :
      SourceTorus.normalizerAction H O hOH e P (Nat.le_of_lt hn) hm ⟨g,hgB⟩ (f x) = f (b x) :=
    SourceActions.normalizerAction_binaryToCommon H O hOH e P (Nat.le_of_lt hn) hm hgH hgO hgB x
  have hd := ExchangedField.binary_displacement hn hm S a
    (fun x hx => (SourceActions.productAction_borel H O hOH e P hgH hgO hgB).le
      (mem_map_of_mem _ hx)) (by
      intro x hx
      let y : BinaryBorel.borel S := ⟨x,hx⟩
      have h : (b y * y⁻¹)^3 ∈ pCore 2 (BinaryBorel.borel S) := by
        rw [←hk,MonoidHom.mem_ker,map_pow,map_mul,map_inv,←he]
        exact hc (f y)
      rw [BinaryBorel.twoCore] at h
      exact h)
  apply MulEquiv.ext
  intro c
  obtain ⟨x,rfl⟩ := ((SourceTorus.commonTorusCoordinates H O e P (Nat.le_of_lt hn) hm).surjective.comp
    (BinaryBorel.productMap_surjective S)) c
  change SourceTorus.normalizerAction H O hOH e P (Nat.le_of_lt hn) hm ⟨g,hgB⟩ (f x) = f x
  rw [he]
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul,←MonoidHom.mem_ker,hk,BinaryBorel.twoCore]
  exact hd x x.property

/-- Cubic displacement on the constructed torus forces field order four,
or puts every original T ∩ L commutator in the full intrinsic Borel two-core. -/
theorem ExchangedTorusAction.field_four_or_commutator_le
    {H K X T L M : Subgroup G} {n : ℕ} {hn2 : 2 ≤ n}
    (h : ExchangedTorusAction H K X T L M n hn2)
    [IsQuasisimple (Chapter13.Section08.Source.starImage H K)] :
    n = 2 ∨ ⁅T ⊓ L,conjugateSpanBy K T ⊓ M⁆ ≤
      (conjugateSpanBy K T ⊓ M).pCoreIn 2 := by
  by_cases hn : n = 2
  · exact Or.inl hn
  have hng : 2 < n := by omega
  obtain ⟨t,ht,hTH,htn,hOH,e,P,hm,hnB,he,hP,hBeq,hMeq,hXB,heven,hker,hf,h9,hcube⟩ := h
  right
  rw [←hBeq]
  apply commutator_le.mpr
  intro s hs x hx
  have hsT : s ∈ T := hs.1
  let s' : (T ⊓ L : Subgroup G) := ⟨s,hs⟩
  let x' : SourceTorus.chosenLift H (conjugateSpanBy K T) hOH P := ⟨x,hx⟩
  have hα := torus_action_eq_one_of_cube H (conjugateSpanBy K T) hOH e P hng hm
    (hTH hsT) (le_normalizer_conjugateSpanBy K T hsT) (hnB hsT) (hcube s')
  have hfix := SourceTorus.normalizerAction_toCommonTori H (conjugateSpanBy K T) hOH e P hn2 hm
    ⟨s,hnB hsT⟩ x'
  rw [hα] at hfix
  change SourceTorus.toCommonTori H (conjugateSpanBy K T) hOH e P hn2 hm x' =
    SourceTorus.toCommonTori H (conjugateSpanBy K T) hOH e P hn2 hm
      ((SourceTorus.chosenLift H (conjugateSpanBy K T) hOH P).normalizerMonoidHom
        ⟨s,hnB hsT⟩ x') at hfix
  let d := (SourceTorus.chosenLift H (conjugateSpanBy K T) hOH P).normalizerMonoidHom
    ⟨s,hnB hsT⟩ x' * x'⁻¹
  have hd : d ∈ pCore 2 (SourceTorus.chosenLift H (conjugateSpanBy K T) hOH P) := by
    rw [←hker,MonoidHom.mem_ker]
    change SourceTorus.toCommonTori _ _ _ _ _ _ _ (_ * _) = 1
    rw [map_mul,map_inv,←hfix]
    exact mul_inv_cancel _
  exact mem_map_of_mem _ hd

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))

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
/-- Apply the field-action restriction to the original constructed torus.
Its full marked data is retained alongside the field/core alternative. -/
theorem SourceHypothesis.original_abelian_exchanged_field_restriction
    (hn : ¬ (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    ExchangedTorusAction H K (D.fullSetup hZ T z).L₁ T L (M L) n hn2 ∧
      (n = 2 ∨ ⁅(T : Subgroup G) ⊓ L,conjugateSpanBy K (T : Subgroup G) ⊓ M L⁆ ≤
        (conjugateSpanBy K (T : Subgroup G) ⊓ M L).pCoreIn 2) := by
  have ht := S.original_abelian_exchanged_torus_action D hZ z hz hTz hTV hbound hTI hns
    hH hKH hK hgen hn hn2 hm
  let : IsQuasisimple (Chapter13.Section08.Source.starImage H K) :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  exact ⟨ht,ht.field_four_or_commutator_le⟩

include hz hTV hTz hbound hTI hns hH in
/-- The original reduced actor retains both component models and every marked
Borel conclusion. Above field order four, its original T ∩ L fixes the Borel
modulo the full intrinsic two-core. -/
theorem SourceHypothesis.original_abelian_reduced_field_restrictions :
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
            ExchangedTorusAction J K (D.fullSetup hZ T z).L₁ T L (M L) n hn2 ∧
            (n = 2 ∨ ⁅(T : Subgroup G) ⊓ L,K₀ ⊓ M L⁆ ≤ (K₀ ⊓ M L).pCoreIn 2))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,halt⟩ :=
    S.original_abelian_reduced_torus_actions D hZ z hz hTz hTV hbound hTI hns hH
  have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left :
      conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hKJ,?_⟩
  rcases halt with hnormal | ⟨hn,hi,n,hn2,heven,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB,hcore,ht⟩
  · exact Or.inl hnormal
  · let : IsQuasisimple (Chapter13.Section08.Source.starImage
        (conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)) K) :=
      hq.of_mulEquiv (componentStarEquiv _ K hKle hKJ)
    exact Or.inr ⟨hn,hi,n,hn2,heven,hm,hmstar,hr,hLB,hOT,hMeq,hsol,hrank,hnB,hcore,ht,
      ht.field_four_or_commutator_le⟩

end CFSG.Quasithin.Chapter12.Section06
