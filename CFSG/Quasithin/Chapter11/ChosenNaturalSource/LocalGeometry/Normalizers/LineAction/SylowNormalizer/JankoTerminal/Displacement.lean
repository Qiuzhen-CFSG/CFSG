module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.SmallAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Flags
public import Theory.GroupTheory.PCoreQuotientInnerSupplement
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The displacement subgroup in the field-four J₁ configuration

For the actual residual Y, take X to be the part of the odd Sylow supplement
inside L that acts trivially on Y/O₂(Y), and put Q = [X,T]. The literal
quotient-action kernel gives T ∩ C_G(Y/O₂(Y)) = O₂(YT), so Q lies in that
radical. The inner-action hypothesis also gives T = (T ∩ Y)O₂(YT).
Characteristic two in LT and the disjointness of the odd supplement from T
show that Q is nontrivial whenever X is nontrivial.

The final applications reduce the two terminal contradictions of 3.3.16 to
their geometric inputs: common normalization for SL₃, or normalization, the
order bound and nontrivial Y-action for Sp₄. The construction of the cubic X,
these remaining geometric assertions, and the J₁ configuration itself remain
with the assembly owner qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.16, printed pp.590--591.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}
    {A : OddSupplement T} (E : JankoConfiguration S f A)
namespace JankoConfiguration

/-- The ambient kernel of the original action on Y/O₂(Y). -/
def sectionCentralizer : Subgroup G :=
  (coreQuotientAction (f.Li E.index)).ker.map (normalizer (f.Li E.index : Set G)).subtype

/-- The source X = C_{A ∩ L}(Y/O₂(Y)), using the literal quotient action. -/
def oddSectionCentralizer : Subgroup G := A.subgroup ⊓ L ⊓ E.sectionCentralizer

/-- The source commutator Q = [X,T]. -/
def displacement : Subgroup G := ⁅E.oddSectionCentralizer, (T : Subgroup G)⁆

/-- The section centralizer is normal in the normalizer of the residual. -/
theorem sectionCentralizer_normalized :
    normalizer (f.Li E.index : Set G) ≤ normalizer (E.sectionCentralizer : Set G) := by
  intro g hg
  apply (coreQuotientAction (f.Li E.index)).ker.le_normalizer_map
    (normalizer (f.Li E.index : Set G)).subtype
  exact ⟨⟨g,hg⟩,(coreQuotientAction (f.Li E.index)).ker.normalizer_eq_top ▸ mem_top _,rfl⟩

/-- The odd supplement normalizes T, so its displacement lies in T. -/
theorem displacement_le_sylow : E.displacement ≤ T :=
  le_normalizer_iff_commutator_le_right.mp
    ((inf_le_left.trans inf_le_left : E.oddSectionCentralizer ≤ A.subgroup).trans A.normalizes)

/-- No commutativity assumption is needed on the displacement two-group. -/
theorem displacement_isTwoGroup : IsPGroup 2 E.displacement :=
  T.isPGroup'.to_le E.displacement_le_sylow

/-- The quotient-action kernel contains the displacement. -/
theorem displacement_le_sectionCentralizer : E.displacement ≤ E.sectionCentralizer :=
  (commutator_mono (show E.oddSectionCentralizer ≤ E.sectionCentralizer from inf_le_right) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((f.sylow_normalizes_Li E.index).trans E.sectionCentralizer_normalized))

/-- The original Sylow subgroup normalizes its displacement with X. -/
theorem sylow_normalizes_displacement :
    (T : Subgroup G) ≤ normalizer (E.displacement : Set G) :=
  normalizer_commutator_ge_right _ _

/-- The section centralizer cuts T in exactly the source radical. -/
theorem sectionCentralizer_inf_sylow
    (hc : center (f.Li E.index ⧸ pCore 2 (f.Li E.index)) = ⊥) :
    (T : Subgroup G) ⊓ E.sectionCentralizer = f.Ri E.index := by
  let Y := f.Li E.index
  let J := Y ⊔ (T : Subgroup G)
  let hn : J ≤ normalizer (Y : Set G) := sup_le Y.le_normalizer (f.sylow_normalizes_Li E.index)
  let a := (coreQuotientAction Y).comp (inclusion hn)
  have he : a = pCoreJoinAction 2 (f.sylow_normalizes_Li E.index) := by
    ext g x
    induction x using Quotient.inductionOn with | h x => rfl
  have hk : a.ker = pCore 2 J := by
    rw [he]
    exact pCoreJoinAction_kernel 2 (f.sylow_normalizes_Li E.index) T.isPGroup' hc
  apply le_antisymm
  · rintro g ⟨hgT,hgK⟩
    have hgJ : g ∈ J := mem_sup_right hgT
    have hga : (⟨g,hgJ⟩ : J) ∈ a.ker := by
      obtain ⟨b,hb,hbg⟩ := hgK
      have hb' : b = inclusion hn ⟨g,hgJ⟩ := Subtype.ext hbg
      change inclusion hn ⟨g,hgJ⟩ ∈ (coreQuotientAction Y).ker
      exact hb' ▸ hb
    rw [hk] at hga
    exact mem_map_of_mem J.subtype hga
  · intro g hgR
    refine ⟨localRadical_le_sylow _ hgR,?_⟩
    obtain ⟨r,hr,rfl⟩ := hgR
    exact ⟨inclusion hn r,show r ∈ a.ker from hk ▸ hr,rfl⟩

/-- The displacement belongs to the literal O₂(YT). -/
theorem displacement_le_radical
    (hc : center (f.Li E.index ⧸ pCore 2 (f.Li E.index)) = ⊥) :
    E.displacement ≤ f.Ri E.index :=
  (le_inf E.displacement_le_sylow E.displacement_le_sectionCentralizer).trans_eq
    (E.sectionCentralizer_inf_sylow hc)

private theorem residual_center_eq_bot (P : FlagInput S f) (i : Fin 2) :
    center (f.Li i ⧸ pCore 2 (f.Li i)) = ⊥ := by
  let : Group.IsPerfect (f.Li i) := localResidual_perfect _
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := P.model i
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show (4 : ℕ) = 2 ^ 2 from rfl).le.trans
      (Nat.pow_le_pow_right (by decide) S.nonbinary)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
  let : IsSimpleGroup (f.Li i ⧸ pCore 2 (f.Li i)) := e.isSimpleGroup
  rcases (inferInstance : (center (f.Li i ⧸ pCore 2 (f.Li i))).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative (f.Li i ⧸ pCore 2 (f.Li i))
      (center_eq_top_iff.mp ht)).elim

/-- The actual PSL₂ residual models discharge the centerless-quotient premise. -/
theorem displacement_le_source_radical :
    E.displacement ≤ f.Ri E.index :=
  E.displacement_le_radical (residual_center_eq_bot (invariantFlag_geometry D S f).2.2 E.index)

/-- Inner action on the quotient factors T through its inner intersection and O₂(YT). -/
theorem sylow_eq_intersection_sup_radical :
    (T : Subgroup G) = ((T : Subgroup G) ⊓ f.Li E.index) ⊔ f.Ri E.index := by
  have P := (invariantFlag_geometry D S f).2.2
  obtain ⟨U,hU⟩ := NormalSylowQuotientAction.intersection_sylow T (f.Li E.index)
    (f.sylow_normalizes_Li E.index)
  have hUT : (U : Subgroup (f.Li E.index)).map (f.Li E.index).subtype =
      (T : Subgroup G) ⊓ f.Li E.index := by
    rw [hU,subgroupOf_map_subtype,inf_comm]
  have he := sup_core_factor_of_inner_action (p := 2) (f.Li E.index) (T : Subgroup G)
    (f.sylow_normalizes_Li E.index) T.isPGroup' (residual_center_eq_bot P E.index)
    U (hUT ▸ inf_le_left) (fun t => E.inner t)
  rw [hUT] at he
  exact he

/-- Characteristic two forces a nontrivial odd X to move T. -/
theorem displacement_ne_bot (hne : E.oddSectionCentralizer ≠ ⊥) : E.displacement ≠ ⊥ := by
  intro hz
  let J := L ⊔ (T : Subgroup G)
  have hcore : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hHe : J ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer.join_characteristicTwo S.source)
  have hXT : E.oddSectionCentralizer ≤ (T : Subgroup G) :=
    ((le_inf (inf_le_left.trans inf_le_right |>.trans le_sup_left)
      ((commutator_eq_bot_iff_le_centralizer.mp hz).trans (centralizer_le hcore))).trans hHe).trans hcore
  apply hne
  exact bot_unique ((le_inf hXT (inf_le_left.trans inf_le_left)).trans_eq A.disjoint.eq_bot)

/-- The SL₃ terminal application, retaining its geometric normalization premises. -/
theorem false_of_displacement_common_normal (hne : E.oddSectionCentralizer ≠ ⊥)
    (hLQ : L ≤ normalizer (E.displacement : Set G))
    (hKQ : E.component ≤ normalizer (E.displacement : Set G)) : False :=
  E.false_of_common_normal (E.displacement_le_sylow.trans le_sup_right)
    (E.displacement_ne_bot hne) (sup_le hLQ E.sylow_normalizes_displacement) hKQ

/-- The Sp₄ terminal application of the order-nineteen obstruction to the actual Q. -/
theorem false_of_displacement_small
    (hsmall : Nat.card E.displacement ≤ 2 ^ 16)
    (hn : E.component ≤ normalizer (E.displacement : Set G))
    (hmoves : ¬ f.Li E.index ≤ centralizer (E.displacement : Set G)) : False :=
  E.false_of_small_twoGroup E.displacement_isTwoGroup hsmall hn hmoves

end JankoConfiguration
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
