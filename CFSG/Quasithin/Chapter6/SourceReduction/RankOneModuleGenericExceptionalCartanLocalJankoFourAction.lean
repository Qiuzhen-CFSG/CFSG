module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourRecognition
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualEmbeddingJankoFour

/-!
# The entire original Cartan actor on J₄

Conjugation on the normal containing component, followed by its literal
two-core quotient marking and the inner-automorphism equivalence of J₄,
gives a surjection from the original overgroup to the concrete J₄ carrier.
The original residual, full Sylow and both Cartan subgroups are transported
along this same map. In particular the entire left Cartan intersection remains
cyclic and odd, permutes with the Sylow and generates a solvable group together
with it and the right cubic, while retaining its failure to normalize the
residual. This supplies the actual configuration for the remaining finite J₄
normalization argument.

The existing private local-component transport is reused through `import all`
without changing its public boundary.

Source: Aschbacher--Smith, The Classification of Quasithin Groups, II,
5.1.13, printed p.637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private def jankoFourInnerEquiv : Janko4.Model ≃* MulAut Janko4.Model :=
  MulEquiv.ofBijective MulAut.conj
    ⟨conj_injective_of_center_eq_bot Janko4.model_center_eq_bot,
      Janko4.AdequateLocal.conj_surjective⟩

/-- The same entire Cartan intersection acts on the actual J₄ carrier.
The quotient, full Sylow, local A₅ section and right cubic all remain literal. -/
theorem normal_jankoFour_native_action
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) :
    ∃ (f : Y →* Janko4.Model) (S : Sylow 2 Janko4.Model),
      Function.Surjective f ∧
      (∀ x : C, f x = e (QuotientGroup.mk' (pCore 2 C) x)) ∧
      (S : Subgroup Janko4.Model) = ((T : Subgroup G).subgroupOf Y).map f ∧
      let R := ((residual H).subgroupOf Y).map f
      let D := (A.subgroupOf Y).map f
      let E := (B.subgroupOf Y).map f
      R ∈ ChapterA.Section03.localCComponents S ∧
      (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model) ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      Nat.card B = 3 ∧ Nat.card E = 3 ∧ E ≤ R ∧
      IsCyclic D ∧ Odd (Nat.card D) ∧ E ≤ normalizer (D : Set Janko4.Model) ∧
      (D : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (D : Set Janko4.Model) ∧
      Group.IsSolvable ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) ∧
      ¬ D ≤ normalizer (R : Set Janko4.Model) ∧ ¬ D ≤ E := by
  have hfour := residual_section_of_jankoFour h hH hgen hY hescape hR C hC hRC e
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let a₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ a₀ (pCore_map_iso 2 a₀)
    obtain ⟨F,_,_,hF,⟨b₀⟩⟩ := hfour
    exact ⟨eq.symm.trans (b₀.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  have hB := right_hall_card_three_of_residual_A5 h hH hgen c hA5
  have hTY := hH.1.1.2.trans hY.2
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hBY := (c.right_le.trans inf_le_right).trans hY.2
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  let g := normalQuotientAction C (pCore 2 C)
  let a := (MulAut.congr e).trans jankoFourInnerEquiv.symm
  let f := a.toMonoidHom.comp g
  have hf (x : C) : f x = e (QuotientGroup.mk' (pCore 2 C) x) := by
    apply jankoFourInnerEquiv.injective
    change jankoFourInnerEquiv (jankoFourInnerEquiv.symm (MulAut.congr e (g x))) = _
    rw [jankoFourInnerEquiv.apply_symm_apply,normalQuotientAction_inner,MulAut.congr_conj]
    rfl
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨x,hx⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 C)) z
    exact ⟨x,(hf x).trans hx⟩
  let S := (T.subtype hTY).mapSurjective hfs
  let R := ((residual H).subgroupOf Y).map f
  let D := (A.subgroupOf Y).map f
  let E := (B.subgroupOf Y).map f
  have hl : (residual H).subgroupOf Y ∈ ChapterA.Section03.localCComponents (T.subtype hTY) :=
    ((Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩).1
  have hlR : R ∈ ChapterA.Section03.localCComponents S :=
    local_image_of_normal_quotient (T.subtype hTY) _ C hl hRC' f e hf
  have hSR : (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model) := by
    apply (map_mono (f := f) ?_).trans (le_normalizer_map f)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hkernel (K : Subgroup Y) (hKC : K ≤ C) : IsPGroup 2 (f.subgroupMap K).ker := by
    have hker : (f.subgroupMap K).ker ≤ (pCore 2 C).comap (inclusion hKC) := by
      intro k hk
      have hfk : f (k : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      change f ((inclusion hKC k : C) : Y) = 1 at hfk
      rw [hf (inclusion hKC k)] at hfk
      change inclusion hKC k ∈ pCore 2 C
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (hfk.trans e.map_one.symm)
    exact (pCore_isPGroup.comap_of_injective (inclusion hKC)
      (inclusion_injective hKC)).to_le hker
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let b := e₀.trans (subgroupOfEquivOfLe hRY).symm
  let er := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans
    ((f.subgroupMap ((residual H).subgroupOf Y)).pCoreQuotientEquiv
      (f.subgroupMap_surjective _) (hkernel _ hRC'))
  have hBR : B.subgroupOf Y ≤ (residual H).subgroupOf Y :=
    comap_mono (Global.right_cartan_le_residual c)
  have hEc : Nat.card E = 3 := by
    let r := f.subgroupMap (B.subgroupOf Y)
    have htwo := hkernel (B.subgroupOf Y) (hBR.trans hRC')
    have hc : Nat.card (B.subgroupOf Y) = 3 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv,hB]
    have hodd : Odd (Nat.card r.ker) := (show Odd (Nat.card (B.subgroupOf Y)) by
      rw [hc]; decide).of_dvd_nat r.ker.card_subgroup_dvd_card
    have hz : r.ker = ⊥ := by
      obtain ⟨k,hk⟩ := htwo.exists_card_eq
      have hk0 : k = 0 := by
        by_contra hk0
        exact hodd.not_two_dvd_nat (by rw [hk]; exact dvd_pow_self 2 hk0)
      exact card_eq_one.mp (by rw [hk,hk0,pow_zero])
    exact (Nat.card_congr (MulEquiv.ofBijective r
      ⟨(MonoidHom.ker_eq_bot_iff r).mp hz,f.subgroupMap_surjective _⟩).toEquiv).symm.trans hc
  obtain ⟨hcyc,hodd,hED,hout,_,hnot⟩ := cartan_action_escape h hH hgen c hY hescape C hRC'
  have hD : ((A.subgroupOf Y).map g).map a.toMonoidHom = D := map_map _ _ _
  have hE : ((B.subgroupOf Y).map g).map a.toMonoidHom = E := map_map _ _ _
  have hRmap : (((residual H).subgroupOf Y).map g).map a.toMonoidHom = R := map_map _ _ _
  have hcycD : IsCyclic D := by
    rw [←hD]
    let := hcyc
    exact isCyclic_of_surjective (a.toMonoidHom.subgroupMap _) (a.toMonoidHom.subgroupMap_surjective _)
  have hoddD : Odd (Nat.card D) := by
    rw [←hD,card_map_of_injective a.injective]
    exact hodd
  have hED' : E ≤ normalizer (D : Set Janko4.Model) := by
    rw [←hD,←hE]
    exact (map_mono hED).trans (le_normalizer_map a.toMonoidHom)
  have hout' : ¬ D ≤ normalizer (R : Set Janko4.Model) := by
    rw [←hD,←hRmap,←map_equiv_normalizer_eq]
    exact fun hn => hout ((map_le_map_iff_of_injective a.injective).mp hn)
  have hnot' : ¬ D ≤ E := by
    rw [←hD,←hE]
    exact fun hn => hnot ((map_le_map_iff_of_injective a.injective).mp hn)
  let JY := (A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y) ⊔ B.subgroupOf Y
  have hLH : ¬ L ≤ H := by
    intro hh
    exact hescape (inf_le_left.trans ((c.left_le.trans (inf_le_left.trans hh)).trans
      (le_normalizer_residual H)))
  have prep := cartanPreparation_of_not_le h hH hgen hLH
  let M := normalizer (L : Set G) ⊓ H
  let V := localBorel T L ⊔ M
  let : Group.IsSolvable (localBorel T L) := prep.borel_solvable
  let : Group.IsSolvable M := prep.intersection_solvable
  let : Group.IsSolvable V := Group.isSolvable_sup_of_normalizes _ _ prep.intersection_normalizes
  have hJV : JY.map Y.subtype ≤ V := by
    rw [Subgroup.map_sup,Subgroup.map_sup,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hTY,
      map_subgroupOf_eq_of_le hBY]
    exact sup_le (sup_le ((inf_le_left.trans c.left_le).trans le_sup_left)
      ((le_inf h.sylow_normalizes hH.1.1.2).trans le_sup_right))
      (c.right_le.trans le_sup_right)
  let : Group.IsSolvable JY := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hJV).comp
      (JY.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    ((inclusion_injective hJV).comp (JY.equivMapOfInjective Y.subtype Y.subtype_injective).injective)
  have hsol : Group.IsSolvable ((D ⊔ (S : Subgroup Janko4.Model)) ⊔ E : Subgroup Janko4.Model) := by
    have hh : Group.IsSolvable (JY.map f) :=
      Group.isSolvable_of_surjective (f.subgroupMap_surjective JY)
    have he : JY.map f = (D ⊔ (S : Subgroup Janko4.Model)) ⊔ E := by
      change ((A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y) ⊔ B.subgroupOf Y).map f = _
      rw [Subgroup.map_sup,Subgroup.map_sup]
      rfl
    rw [he] at hh
    exact hh
  exact ⟨f,S,hfs,hf,rfl,hlR,hSR,hfour.of_mulEquiv er.symm,hB,hEc,map_mono hBR,
    hcycD,hoddD,hED',c.image_intersection_permutes_sylow h.sylow_normalizes hTY f,
    hsol,hout',hnot'⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
