module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Endgame
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.ComponentDecomposition
public import Theory.Representation.PSL3Two.PairedNaturalDual.EmbeddedMarking
public import Theory.Representation.BinaryConjugationSection.SupportImages
public import Theory.GroupTheory.CComponent.PairPermutation
public import Theory.GroupTheory.CComponent.ResidualMarking
public import Theory.GroupTheory.NormalSylowQuotientAction.MarkedLift
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.CoordinateEmbedding

/-!
# Two component markings on the original quotient

The prescribed isomorphisms K/O₂(K) and K⁺/O₂(K⁺) embed the actual
components in Mc/O₂(Mc). Their literal natural--dual sections embed in the
same U/Z. Conjugation permutes the component pair; distinct support images
identify each component normalizer with its subspace stabilizer. The
Gaschütz component sum constructs the fixed supplement. Extending the two
component actions now constructs the simultaneous paired marking, with all
four restrictions retained. Original outer actors give the witnesses used
by the checked endpoint and Sylow contradiction.

The full sections, cross-centralization and separation are precisely the
14.6.22--23 inputs owned by qt-e-suitable-component-supports. SourceSections
discharges the joined-section and outer-actor premises. Original 14.6.18
remains with qt-e-14625-source; qt-e-suitable-component-marking retains the
14.6.24 assembly and qt-e-suitable-existence retains final suitable choice.
This does not assert unconditional 14.6.24.

Source: Aschbacher--Smith 14.6.21--24, printed pp.1038--1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open BinaryLinearThree.NaturalDual Subgroup.NormalSylowQuotientAction
variable {G : Type*} [Group G] [Finite G]

/-- Construct all simultaneous markings from the literal component sections
and apply the two-component exclusion in the unchanged original setup. -/
theorem source_no_paired_components_of_original_sections
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (K Kplus : Subgroup G) (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hKplus : (Kplus.subgroupOf Mc).IsCComponent)
    (hall : ∀ J : Subgroup Mc, J.IsCComponent → J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eKplus : (Kplus ⧸ pCore 2 Kplus) ≃* BinaryLinearThree.Group)
    (d : BinaryConjugationSection K ⁅conjugateSpanBy (localModule T M) Mc,K⁆
      (centralInvolutions T) (action.comp (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))))
    (d' : BinaryConjugationSection Kplus ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆
      (centralInvolutions T) (action.comp (eKplus.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Kplus)))))
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    (hcrossRev : ⁅⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆,K⁆ = ⊥)
    (hsep : ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ⊓
      ⁅conjugateSpanBy (localModule T M) Mc,Kplus⁆ ≤ centralInvolutions T)
    (s : (Mc ⊓ normalizer (K : Set G) : Subgroup G))
    (hs : markedCoreAction 2 K eK ⟨s,s.property.2⟩ ∉ MulAut.innerSubgroup BinaryLinearThree.Group)
    (t : (Mc ⊓ normalizer (Kplus : Set G) : Subgroup G))
    (ht : markedCoreAction 2 Kplus eKplus ⟨t,t.property.2⟩ ∉ MulAut.innerSubgroup BinaryLinearThree.Group) :
    False := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let Z := centralInvolutions T
  let π := QuotientGroup.mk' (pCore 2 Mc)
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  let S := ⁅U,K⁆
  let S' := ⁅U,Kplus⁆
  have hSU : S ≤ U := le_normalizer_iff_commutator_le_left.mp (hKM.trans (le_normalizer_conjugateSpanBy _ _))
  have hS'U : S' ≤ U := le_normalizer_iff_commutator_le_left.mp (hKplusM.trans (le_normalizer_conjugateSpanBy _ _))
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  let : (Z.subgroupOf U).Normal := inferInstance
  obtain ⟨ρ,c,_⟩ := BinaryConjugationSection.exists_descended_actor Mc U Z h.UH_le_H
    (h.point_lt.le.trans (le_conjugateSpanBy _ _)) (le_normalizer_conjugateSpanBy _ _)
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) π
    (QuotientGroup.mk'_surjective _) (by
      intro a ha b hb
      have hcore : (a:G) ∈ Mc.pCoreIn 2 :=
        mem_map_of_mem Mc.subtype ((QuotientGroup.eq_one_iff a).mp ha)
      have hc := h.commutator_UH_QH_le_point (commutator_mem_commutator hb hcore)
      simpa only [commutatorElement_inv] using Z.inv_mem hc)
  let f := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f' := eKplus.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Kplus))
  have hf : Function.Surjective f := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hf' : Function.Surjective f' := eKplus.surjective.comp (QuotientGroup.mk'_surjective _)
  let j := subgroupOfEquivOfLe hKM
  let j' := subgroupOfEquivOfLe hKplusM
  let ej := (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans eK
  let ej' := (QuotientGroup.congr _ _ j' (pCore_map_iso 2 j')).trans eKplus
  obtain ⟨κ,hκ,hr,hmark⟩ := exists_twoCore_component_marking (K.subgroupOf Mc) hK ej
  obtain ⟨κ',hκ',hr',hmark'⟩ := exists_twoCore_component_marking (Kplus.subgroupOf Mc) hKplus ej'
  have hκf (k : K) : π (inclusion hKM k) = κ (f k) := (hmark (j.symm k)).symm
  have hκf' (k : Kplus) : π (inclusion hKplusM k) = κ' (f' k) := (hmark' (j'.symm k)).symm
  obtain ⟨emb,hemb,_,heact,herange⟩ := c.exists_coordinate_embedding d hKM hSU
  obtain ⟨emb',hemb',_,heact',herange'⟩ := c.exists_coordinate_embedding d' hKplusM hS'U
  have hact (k : BinaryLinearThree.Group) (v : Space) : ρ (κ k) (emb v) = emb (action k v) := by
    obtain ⟨x,rfl⟩ := hf k
    rw [←hκf]
    exact heact x v
  have hact' (k : BinaryLinearThree.Group) (v : Space) : ρ (κ' k) (emb' v) = emb' (action k v) := by
    obtain ⟨x,rfl⟩ := hf' k
    rw [←hκf']
    exact heact' x v
  have hdis : Disjoint emb.range emb'.range := by
    rw [herange,herange']
    exact c.imageSpace_disjoint S S' d'.kernel_le hsep
  have hSne : S ≠ S' := by
    intro he
    have hh : emb.range = emb'.range := herange.trans ((congrArg c.imageSpace he).trans herange'.symm)
    have hz : emb ((fun _ => 1),0) = 0 := Submodule.disjoint_def.mp hdis _ ⟨_,rfl⟩ (hh ▸ ⟨_,rfl⟩)
    have hv := hemb (hz.trans (map_zero emb).symm)
    have hv0 := congrArg (fun v : Space => v.1 0) hv
    norm_num at hv0
  have hp := relative_cComponent_pair_permutation Mc K Kplus hKM hKplusM hK hKplus hall
  have hnorm := normalizer_commutator_eq_of_permuted_pair Mc U K Kplus
    (le_normalizer_conjugateSpanBy _ _) hp hSne
  have hn₁ : normalizer (κ.range : Set (Source.Hstar Mc)) = subspaceStabilizer ρ emb.range := by
    apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 Mc))
    rw [hr,normalizer_cComponent_quotient hK,←subgroupOf_normalizer_eq hKM,hnorm.1,herange]
    exact (c.subspaceStabilizer_imageSpace S hSU d.kernel_le).symm
  have hn₂ : normalizer (κ'.range : Set (Source.Hstar Mc)) = subspaceStabilizer ρ emb'.range := by
    apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 Mc))
    rw [hr',normalizer_cComponent_quotient hKplus,←subgroupOf_normalizer_eq hKplusM,hnorm.2,herange']
    exact (c.subspaceStabilizer_imageSpace S' hS'U d'.kernel_le).symm
  let N := normalizer (κ.range : Set (Source.Hstar Mc)) ⊓ normalizer (κ'.range : Set (Source.Hstar Mc))
  have hκc : κ.range.IsCComponent := by rw [hr]; exact hK.map_quotient (pCore 2 Mc)
  have hκc' : κ'.range.IsCComponent := by rw [hr']; exact hKplus.map_quotient (pCore 2 Mc)
  have hκN : κ.range ≤ N := le_inf κ.range.le_normalizer
    ((le_cComponentLayer hκc).trans (cComponentLayer_le_normalizer hκc'))
  have hκN' : κ'.range ≤ N := le_inf
    ((le_cComponentLayer hκc').trans (cComponentLayer_le_normalizer hκc)) κ'.range.le_normalizer
  let κN := κ.codRestrict N (fun k => hκN ⟨k,rfl⟩)
  let κN' := κ'.codRestrict N (fun k => hκN' ⟨k,rfl⟩)
  have hiN : Function.Injective κN := by intro x y he; exact hκ (congrArg Subtype.val he)
  have hiN' : Function.Injective κN' := by intro x y he; exact hκ' (congrArg Subtype.val he)
  have hnN : κN.range.Normal := by
    rw [←MonoidHom.subgroupOf_range_eq_of_le κ hκN]
    exact normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (κ.range : Set _) from inf_le_left)
  have hnN' : κN'.range.Normal := by
    rw [←MonoidHom.subgroupOf_range_eq_of_le κ' hκN']
    exact normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (κ'.range : Set _) from inf_le_right)
  have hfixed (k : BinaryLinearThree.Group) (v : Space) : ρ (κ k) (emb' v) = emb' v := by
    obtain ⟨x,rfl⟩ := hf k
    rw [←hκf]
    apply c.fixed_on_imageSpace_of_commutator_le K S'
      (by rw [commutator_comm,hcrossRev]; exact bot_le) (inclusion hKM x) x.property
    rw [←herange']; exact ⟨v,rfl⟩
  have hfixed' (k : BinaryLinearThree.Group) (v : Space) : ρ (κ' k) (emb v) = emb v := by
    obtain ⟨x,rfl⟩ := hf' k
    rw [←hκf']
    apply c.fixed_on_imageSpace_of_commutator_le Kplus S
      (by rw [commutator_comm,hcross]; exact bot_le) (inclusion hKplusM x) x.property
    rw [←herange]; exact ⟨v,rfl⟩
  have hmodels (J : Subgroup G) (hJM : J ≤ Mc) (hc : (J.subgroupOf Mc).IsCComponent) :
      ComponentSupports.Classification.ComponentQuotientModels J := by
    rcases hall _ hc with he | he
    · have he' : J = K := by
        simpa only [map_subgroupOf_eq_of_le hJM,
          map_subgroupOf_eq_of_le hKM] using congrArg (map Mc.subtype) he
      subst J; exact Or.inl ⟨eK⟩
    · have he' : J = Kplus := by
        simpa only [map_subgroupOf_eq_of_le hJM,
          map_subgroupOf_eq_of_le hKplusM] using congrArg (map Mc.subtype) he
      subst J; exact Or.inl ⟨eKplus⟩
  have hspan : emb.range ⊔ emb'.range ⊔ fixedSpace ρ ⊤ = ⊤ := by
    have hh := ComponentSupports.source_full_component_sum_sup_fixed_of_models
      hG T hempty hM hunique hmany hcard e hab hsolv hmodels (ρ.comp π) c
    apply top_unique
    rw [←hh]
    apply sup_le
    · apply iSup_le
      intro J
      rcases hall J J.property with he | he
      · rw [he,map_subgroupOf_eq_of_le hKM,←herange]
        exact le_sup_left.trans le_sup_left
      · rw [he,map_subgroupOf_eq_of_le hKplusM,←herange']
        exact le_sup_right.trans le_sup_left
    · have hfspace : Representation.OneCohomology.fixed (ρ.comp π) = fixedSpace ρ ⊤ := by
        ext v
        constructor
        · intro hv a
          obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) a.val
          change ρ a.val v = v
          rw [←hx]
          exact hv x
        · intro hv x
          exact hv ⟨π x,mem_top _⟩
      rw [hfspace]
      exact le_sup_right
  have hspanN : emb.range ⊔ emb'.range ⊔ fixedSpace (ρ.comp N.subtype) ⊤ = ⊤ := by
    apply top_unique
    rw [←hspan]
    apply sup_le_sup_left
    intro v hv n
    exact hv ⟨n,mem_top _⟩
  obtain ⟨m,hm,hm',hl₁,hr₁,hl₂,hr₂⟩ := Paired.exists_marking_of_component_embeddings
    (ρ.comp N.subtype) κN κN' hiN hiN' hnN hnN' emb emb' hemb hemb'
    (fun a v hv => (show a.val ∈ subspaceStabilizer ρ emb.range from hn₁ ▸ a.property.1) v |>.mpr hv)
    (fun a v hv => (show a.val ∈ subspaceStabilizer ρ emb'.range from hn₂ ▸ a.property.2) v |>.mpr hv)
    hact hact' hfixed hfixed' hdis hspanN
  have hN : N = subspaceStabilizer ρ m.leftEmbedding.range ⊓
      subspaceStabilizer ρ m.rightEmbedding.range := by rw [hm,hm']; exact congrArg₂ (· ⊓ ·) hn₁ hn₂
  have hspanM : m.leftEmbedding.range ⊔ m.rightEmbedding.range ⊔ fixedSpace ρ ⊤ = ⊤ := by
    rwa [hm,hm']
  have hperm : ∀ a : Source.Hstar Mc,
      (m.leftEmbedding.range.map (ρ a) = m.leftEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.rightEmbedding.range) ∨
      (m.leftEmbedding.range.map (ρ a) = m.rightEmbedding.range ∧
        m.rightEmbedding.range.map (ρ a) = m.leftEmbedding.range) := by
    intro a
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) a
    rw [hm,hm',herange,herange']
    have hmap (J : Subgroup G) :
        (⁅U,J⁆ : Subgroup G).map (MulAut.conj (x:G)).toMonoidHom =
          ⁅U,J.map (MulAut.conj (x:G)).toMonoidHom⁆ := by
      rw [map_commutator]
      congr 1
      exact mem_normalizer_iff_map_conj_eq.mp (c.normalized x.property)
    have hleft := c.imageSpace_conjBy S hSU x
    have hright := c.imageSpace_conjBy S' hS'U x
    change c.imageSpace (S.map (MulAut.conj (x:G)).toMonoidHom) =
      (c.imageSpace S).map (ρ (π x)) at hleft
    change c.imageSpace (S'.map (MulAut.conj (x:G)).toMonoidHom) =
      (c.imageSpace S').map (ρ (π x)) at hright
    change ((c.imageSpace S).map (ρ (π x)) = c.imageSpace S ∧
      (c.imageSpace S').map (ρ (π x)) = c.imageSpace S') ∨
      ((c.imageSpace S).map (ρ (π x)) = c.imageSpace S' ∧
      (c.imageSpace S').map (ρ (π x)) = c.imageSpace S)
    rw [←hleft,←hright,hmap K,hmap Kplus]
    rcases hp x x.property with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [ha,hb]; exact Or.inl ⟨rfl,rfl⟩
    · rw [ha,hb]; exact Or.inr ⟨rfl,rfl⟩
  have hnorm₁ : (normalizer (K : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.leftEmbedding.range).comap π := by
    rw [hm,←hn₁,hr,normalizer_cComponent_quotient hK,subgroupOf_normalizer_eq hKM]
  have hnorm₂ : (normalizer (Kplus : Set G)).subgroupOf Mc =
      (subspaceStabilizer ρ m.rightEmbedding.range).comap π := by
    rw [hm',←hn₂,hr',normalizer_cComponent_quotient hKplus,subgroupOf_normalizer_eq hKplusM]
  have hfaith := f9_section_faithful _ h (criticalSection h c)
  let m' : Paired.Marking (ρ.comp N.subtype) := {
    left := m.right
    right := m.left
    leftEmbedding := m.rightEmbedding
    rightEmbedding := m.leftEmbedding
    left_injective := m.right_injective
    right_injective := m.left_injective
    disjoint := m.disjoint.symm
    span := by rw [sup_comm m.rightEmbedding.range m.leftEmbedding.range]; exact m.span
    left_intertwines := m.right_intertwines
    right_intertwines := m.left_intertwines }
  have hcov (a : N) (k : BinaryLinearThree.Group) :
      κ (m.left a k) = (a : Source.Hstar Mc)*κ k*(a : Source.Hstar Mc)⁻¹ :=
    congrArg N.subtype (m'.right_component_covariance
      (hfaith.comp N.subtype_injective) κN hr₁ hl₁ a k)
  have houter
      (A B : Subgroup G) (hAH : A ≤ Mc)
      (eA : (A ⧸ pCore 2 A) ≃* BinaryLinearThree.Group)
      (κA : BinaryLinearThree.Group →* Source.Hstar Mc) (hκA : Function.Injective κA)
      (α : N →* MulAut BinaryLinearThree.Group)
      (hκAq : ∀ k : A, π (inclusion hAH k) = κA (eA (QuotientGroup.mk' (pCore 2 A) k)))
      (hc : ∀ a : N, ∀ k, κA (α a k) = (a:Source.Hstar Mc)*κA k*(a:Source.Hstar Mc)⁻¹)
      (hpair : ∀ x ∈ Mc,
        (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
        (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A))
      (hne : A ≠ B)
      (hAN : ∀ x : Mc, (x:G) ∈ normalizer (A:Set G) → (x:G) ∈ normalizer (B:Set G) → π x ∈ N)
      (s : (Mc ⊓ normalizer (A:Set G) : Subgroup G))
      (hs : markedCoreAction 2 A eA ⟨s,s.property.2⟩ ∉ MulAut.innerSubgroup BinaryLinearThree.Group) :
      ∃ a : N, α a ∉ MulAut.innerSubgroup BinaryLinearThree.Group := by
    have hsB : (s:G) ∈ normalizer (B:Set G) := by
      have hsf := mem_normalizer_iff_map_conj_eq.mp s.property.2
      rcases hpair s s.property.1 with hh | hh
      · exact mem_normalizer_iff_map_conj_eq.mpr hh.2
      · exact (hne (hsf.symm.trans hh.1)).elim
    let a : N := ⟨π ⟨s,s.property.1⟩,hAN ⟨s,s.property.1⟩ s.property.2 hsB⟩
    refine ⟨a,?_⟩
    have he : α a = markedCoreAction 2 A eA ⟨s,s.property.2⟩ := by
      apply MulEquiv.ext
      intro k
      obtain ⟨y,rfl⟩ := eA.surjective k
      obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) y
      apply hκA
      rw [hc,markedCoreAction_mk,←hκAq,←hκAq]
      change π ⟨s,s.property.1⟩ * π (inclusion hAH y) * (π ⟨s,s.property.1⟩)⁻¹ = _
      rw [←map_inv,←map_mul,←map_mul]
      rfl
    rwa [he]
  have hKne : K ≠ Kplus := fun he => hSne (congrArg (fun J => ⁅U,J⁆) he)
  have hmember (x : Mc) (hx : (x:G) ∈ normalizer (K:Set G))
      (hx' : (x:G) ∈ normalizer (Kplus:Set G)) : π x ∈ N := by
    constructor
    · change x ∈ (normalizer (κ.range : Set _)).comap π
      rw [hr,normalizer_cComponent_quotient hK,←subgroupOf_normalizer_eq hKM]
      exact hx
    · change x ∈ (normalizer (κ'.range : Set _)).comap π
      rw [hr',normalizer_cComponent_quotient hKplus,←subgroupOf_normalizer_eq hKplusM]
      exact hx'
  obtain ⟨a,ha⟩ := houter K Kplus hKM eK κ hκ m.left hκf hcov hp hKne hmember s hs
  have hcov' (a : N) (k : BinaryLinearThree.Group) :
      κ' (m.right a k) = (a : Source.Hstar Mc)*κ' k*(a : Source.Hstar Mc)⁻¹ :=
    congrArg N.subtype (m.right_component_covariance (hfaith.comp N.subtype_injective) κN' hl₂ hr₂ a k)
  obtain ⟨b,hb⟩ := houter Kplus K hKplusM eKplus κ' hκ' m.right hκf' hcov'
    (fun x hx => (hp x hx).imp And.symm And.symm) hKne.symm
    (fun x hx hx' => hmember x hx' hx) t ht
  exact source_no_paired_components hG T hempty hM hunique hmany hcard e hab K Kplus
    hKM hKplusM hK hKplus hcross hcrossRev c N m hN hspanM hperm κN κN' hr hr'
    hl₁ hr₁ hl₂ hr₂ hall d.kernel_le d'.kernel_le (herange.symm.trans (congrArg LinearMap.range hm.symm))
    (herange'.symm.trans (congrArg LinearMap.range hm'.symm)) hnorm₁ hnorm₂ a b ha hb eK eKplus
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
