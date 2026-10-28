module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.TwistedRankTwo
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.LinearCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryProperSylowCore.ThreeRank
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import GorensteinWalter.PSL2Cardinality

/-!
# Complete rank-two exclusion in the moved component quotient

The derived binary symplectic carrier is A₆. For the derived binary G₂ carrier,
the original rank-one quotient order divides the residual image order, without
asserting that this image is itself simple. The concrete order forces field
size eight. Its factor nine contradicts the two-core calculation for a proper
full-Sylow overgroup in G₂(2)′.

Together with the untwisted and twisted parabolic arguments this excludes
every rank-two row of the actual Theorem C catalogue, and the full even SL₃
covering row. The final application starts with the original normalizer escape;
all quotients and actions are those of its moved component. The remaining J₁
recognition and terminal obligations belong to qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, A.3.12 and 3.3.12, printed pp.47--48,589--590.
Concrete model imports retain LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The order of the original rank-one quotient divides the order of its actual
image in K/O₂(K); the image need not itself be a simple group. -/
theorem residual_quotient_card_dvd_image :
    Nat.card (f.Li E.index ⧸ pCore 2 (f.Li E.index)) ∣ Nat.card E.residualImage := by
  let q := (QuotientGroup.mk' (pCore 2 E.component)).comp (inclusion E.contains.le)
  have hp : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective E.contains.le)
  have hker : q.ker ≤ pCore 2 (f.Li E.index) := le_sSup ⟨inferInstance,hp⟩
  have hd : Nat.card (f.Li E.index ⧸ pCore 2 (f.Li E.index)) ∣ Nat.card (f.Li E.index ⧸ q.ker) := by
    change (pCore 2 (f.Li E.index)).index ∣ q.ker.index
    exact index_dvd_of_le hker
  have he : q.range = E.residualImage := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact mem_map_of_mem (QuotientGroup.mk' (pCore 2 E.component)) y.property
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv,he] at hd

/-- The literal field marking supplies the exact rank-one order divisor. -/
theorem rank_one_order_dvd_image :
    2^S.field.degree * ((2^S.field.degree)^2 - 1) ∣ Nat.card E.residualImage := by
  have hd := E.residual_quotient_card_dvd_image
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := (invariantFlag_geometry D S f).2.2.model E.index
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := S.field.degree)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rwa [Nat.card_congr (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
    GorensteinWalter.sl2_card_formula,hF] at hd

/-- In the actual binary derived G₂ group the only possible parameter is eight;
its factor nine contradicts the original proper full-Sylow overgroup. -/
theorem quotient_not_binary_g2_derived :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  have hd := E.rank_one_order_dvd_image.trans E.residualImage.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  have hn : S.field.degree < 6 := by
    by_contra h
    have h64 : 64 ∣ 6048 := (pow_dvd_pow 2 (by omega : 6 ≤ S.field.degree)).trans
      ((dvd_mul_right _ _).trans hd)
    norm_num at h64
  have hn2 := S.nonbinary
  have he : S.field.degree = 3 := by
    have hc : S.field.degree = 2 ∨ S.field.degree = 3 ∨ S.field.degree = 4 ∨ S.field.degree = 5 := by omega
    rcases hc with h | h | h | h
    · norm_num [h] at hd
    · exact h
    · norm_num [h] at hd
    · norm_num [h] at hd
  let J := E.residualImage ⊔ E.quotientSylow
  have hJ : J.map e.toMonoidHom ≠ ⊤ := by
    intro hh
    apply E.residualImage_sup_quotientSylow_ne_top
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [hh,map_top_of_surjective _ e.surjective]
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  have hPJ : (P.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup _) ≤ J.map e.toMonoidHom := by
    change (P : Subgroup _).map e.toMonoidHom ≤ _
    rw [hP]
    exact map_mono le_sup_right
  have hcore := Atlas.G2.BinaryProperSylowCore.twoCore_ne_bot
    (P.mapSurjective (f := e.toMonoidHom) e.surjective) _ hJ hPJ
  apply Atlas.G2.BinaryProperSylowCore.nine_not_dvd_of_twoCore_ne_bot _ hcore
  rw [card_map_of_injective e.injective]
  have h9 : 9 ∣ Nat.card E.residualImage := by
    have hh := E.rank_one_order_dvd_image
    rw [he] at hh
    exact (by decide : 9 ∣ 2^3 * ((2^3)^2 - 1)).trans hh
  exact h9.trans (card_dvd_of_le (show E.residualImage ≤ J from le_sup_left))

/-- The derived binary projective symplectic carrier is genuinely A₆. -/
theorem quotient_not_binary_symplectic_derived :
    ¬ Nonempty ((E.component ⧸ pCore 2 E.component) ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rintro ⟨e⟩
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  have hl : E.residualImage ∈ ChapterA.Section03.localCComponents P := hP.symm ▸ E.residualImage_local
  exact E.residualImage_ne_top
    (ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups P hl
      E.componentQuotient_isCComponent le_top
      (Theory.GroupTheory.SolvableSylowOvergroups.of_equiv
        (topEquiv.trans (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix))
        AlternatingSix.ProperSylowOvergroups.isSolvable))
/-- Every rank-two row of the source catalogue is excluded in the literal
component quotient by its genuine model isomorphism. -/
theorem quotient_not_rank_two :
    ¬ Chapter1.Section02.LocalModels.RankTwoTheoremC
      (E.component ⧸ pCore 2 E.component) := by
  intro h
  cases h with
  | linear n hn iso => exact E.quotient_not_even_linear_three hn iso
  | symplectic n hn iso => exact E.quotient_not_even_symplectic_four hn iso
  | g2 n hn iso => exact E.quotient_not_even_g2 hn iso
  | triality n hn iso => exact E.quotient_not_even_triality hn iso
  | ree n hn iso => exact E.quotient_not_ree hn iso
  | symplectic_derived iso => exact E.quotient_not_binary_symplectic_derived iso
  | g2_derived iso => exact E.quotient_not_binary_g2_derived iso
  | tits iso => exact E.quotient_not_tits iso

end MovedComponent

/-- The original escaping normalizer produces a moved component with neither a
rank-two quotient nor a full even linear-three covering quotient. This removes
those branches from the source J₁ recognition problem. -/
theorem exists_moved_component_not_rank_two (f : InvariantFlag c)
    (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      (¬ Chapter1.Section02.LocalModels.RankTwoTheoremC
        (E.component ⧸ pCore 2 E.component)) ∧
      (∀ n, 1 ≤ n → ¬ Chapter1.Section02.LocalModels.IsSL
        (E.component ⧸ pCore 2 E.component) 3 (2^n)) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.quotient_not_rank_two,fun _ hn => E.quotient_not_even_special_linear_three hn⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
