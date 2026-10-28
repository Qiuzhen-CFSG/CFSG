module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourAction
public import Theory.SpecificGroups.Janko4.Model.CubicSylowQuotient
public import Theory.SpecificGroups.Alternating.FiveComponentExtension
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.PermutingSupCard
/-!
# The original J₄ branch with both Hall products

The right Hall complement gives BT = TB. Transport along the original
normal-component action therefore gives an index-three full Sylow product
in J₄. Its intrinsic two-core has order 2²⁰, and its quotient is S₃ with
the Sylow and cubic images marked under the same quotient map.

An S-normalized local A₅ component R has (RS)/O₂(RS) isomorphic to S₅:
the five-point action gives A₅ or S₅, and the former would contradict
self-normalization of a full J₄ Sylow. The restriction of the original
action to H has two-group kernel, since its kernel on O²(H) is a two-group
and H/O²(H) is a two-group. This proves the literal H/O₂(H) is S₅ and
connects that recognition to the original component sieve.

The entire original left actor and its escape condition are retained.
Its normalization of R, the J₄ exclusion and SourceLocalCartanEscape
remain open; neither quotient identification asserts those conclusions.

Source: Aschbacher--Smith, The Classification of Quasithin Groups, II,
5.1.9--13, printed pp.634--637, refs/quasithin.pdf. The imported native
J₄ certificates retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem right_image_permutes
    {T : Sylow 2 G} {L H A B Y : Subgroup G}
    (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hHY : H ≤ Y)
    {Q : Type*} [Group Q] (f : Y →* Q) :
    ((B.subgroupOf Y).map f : Set Q) * (((T : Subgroup G).subgroupOf Y).map f : Set Q) =
      (((T : Subgroup G).subgroupOf Y).map f : Set Q) * ((B.subgroupOf Y).map f : Set Q) := by
  let M := normalizer (L : Set G) ⊓ H
  have hTM : (T : Subgroup G) ≤ M := le_inf hTL hTH
  have hMY : M ≤ Y := inf_le_right.trans hHY
  let j := inclusion hMY
  have hB : ((B.subgroupOf M).map j).map f = (B.subgroupOf Y).map f := by
    congr 1
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact hb
    · intro hx
      exact ⟨⟨x.val,c.right_le hx⟩,hx,rfl⟩
  have hT : (((T : Subgroup G).subgroupOf M).map j).map f =
      ((T : Subgroup G).subgroupOf Y).map f := by
    congr 1
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x.val,hTM hx⟩,hx,rfl⟩
  have hc := c.sylow_complement hTL hTH
  have hprod : ((B.subgroupOf M : Subgroup M) : Set M) *
      ((T : Subgroup G).subgroupOf M : Set M) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨⟨b,t⟩,he⟩ := hc.symm.2 x
    exact ⟨b,b.property,t,t.property,he⟩
  have hprod' : ((T : Subgroup G).subgroupOf M : Set M) *
      (B.subgroupOf M : Set M) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨⟨t,b⟩,he⟩ := hc.2 x
    exact ⟨t,t.property,b,b.property,he⟩
  have hh := congrArg (Set.image (f.comp j)) (hprod.trans hprod'.symm)
  simpa only [Set.image_mul,←coe_map,←map_map,hB,hT] using hh

private theorem cubic_product_index
    (S : Sylow 2 Janko4.Model) (E : Subgroup Janko4.Model)
    (hE : Nat.card E = 3)
    (hp : (E : Set Janko4.Model) * (S : Set Janko4.Model) =
      (S : Set Janko4.Model) * (E : Set Janko4.Model)) :
    (S : Subgroup Janko4.Model).relIndex (E ⊔ (S : Subgroup Janko4.Model)) = 3 := by
  have hd : Disjoint E (S : Subgroup Janko4.Model) := by
    apply disjoint_of_coprime_natCard
    rw [hE,Janko4.OuterReduction.OddIndex.ambient_sylow_card S]
    norm_num
  have hc := card_sup_eq_mul_of_permutes_of_disjoint E (S : Subgroup Janko4.Model) hp hd
  have hi := relIndex_mul_relIndex (⊥ : Subgroup Janko4.Model) (S : Subgroup Janko4.Model)
    (E ⊔ (S : Subgroup Janko4.Model)) bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,hc,hE,
    Janko4.OuterReduction.OddIndex.ambient_sylow_card S] at hi
  omega

private theorem self_normalizing_no_five_image
    {X : Type*} [Group X] [Finite X] (P : Sylow 2 X)
    (hP : normalizer (P : Set X) = (P : Subgroup X))
    (f : X →* alternatingGroup (Fin 5)) (hf : Function.Surjective f) : False := by
  let Q := P.mapSurjective hf
  have hh := P.normalizer_map_surjective f hf
  have hc := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_card Q
  change Nat.card (normalizer ((P : Subgroup X).map f : Set (alternatingGroup (Fin 5)))) = 12 at hc
  rw [←hh,hP] at hc
  have hp := P.isPGroup'.map f
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have h3 : 3 ∣ 2^k := by rw [←hk,hc]; decide
  have h32 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h32

/-- A full-Sylow-normalized A₅ local component of J₄ has S₅, rather than
A₅, as the literal two-core quotient of its Sylow extension. -/
theorem jankoFour_local_five_extension
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model)
    (hR : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (R : Set Janko4.Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) :
    Nonempty (((R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
      pCore 2 (R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
      Equiv.Perm (Fin 5)) := by
  let N := R ⊔ (S : Subgroup Janko4.Model)
  let P := S.subtype (show (S : Subgroup Janko4.Model) ≤ N from le_sup_right)
  let K := R.subgroupOf N
  let : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le R.le_normalizer hn)
  let a := subgroupOfEquivOfLe (show R ≤ N from le_sup_left)
  let aq : (K ⧸ pCore 2 K) ≃* (R ⧸ pCore 2 R) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eK := aq.trans (eF.trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)
  have hgen : K ⊔ (P : Subgroup N) = ⊤ := by
    change R.subgroupOf N ⊔ (S : Subgroup Janko4.Model).subgroupOf N = ⊤
    rw [←subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self N
  obtain ⟨f,hfk,hr,hfK⟩ :=
    Theory.SpecificGroups.Alternating.FiveExtensionAction.cComponent_action
      K (P : Subgroup N) hR P.isPGroup' hgen eK
  have hNP : normalizer (P : Set N) = (P : Subgroup N) := by
    change normalizer ((S : Subgroup Janko4.Model).subgroupOf N : Set N) = _
    rw [←subgroupOf_normalizer_eq (show (S : Subgroup Janko4.Model) ≤ N from le_sup_right)]
    change (normalizer (S : Set Janko4.Model)).subgroupOf N =
      (S : Subgroup Janko4.Model).subgroupOf N
    rw [Janko4.sylow_normalizer_eq S]
  have htop : f.range = ⊤ := by
    rcases hr with ha | ht
    · let g : N →* alternatingGroup (Fin 5) := f.codRestrict _ (fun x => ha ▸ ⟨x,rfl⟩)
      have hg : Function.Surjective g := by
        intro x
        obtain ⟨y,hy⟩ := (show x.val ∈ f.range from ha.symm ▸ x.property)
        exact ⟨y,Subtype.ext hy⟩
      exact (self_normalizing_no_five_image P hNP g hg).elim
    · exact ht
  have hfs : Function.Surjective f := MonoidHom.range_eq_top.mp htop
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfs)⟩

/-- Both original Hall products survive the same normal J₄ action, with
marked right-cubic quotient and the residual's full Sylow extension. -/
theorem normal_jankoFour_native_hall_geometry
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
      (E : Set Janko4.Model) * (S : Set Janko4.Model) =
        (S : Set Janko4.Model) * (E : Set Janko4.Model) ∧
      Nat.card (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) = 3 * 2^21 ∧
      Nat.card (pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) = 2^20 ∧
      Nonempty (((R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
        pCore 2 (R ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
        Equiv.Perm (Fin 5)) ∧
      (∃ e₃ : ((E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) ⧸
          pCore 2 (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model)) ≃*
          Equiv.Perm (Fin 3),
        let N := E ⊔ (S : Subgroup Janko4.Model)
        let q := e₃.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
        Nat.card (((S : Subgroup Janko4.Model).subgroupOf N).map q) = 2 ∧
        Nat.card ((E.subgroupOf N).map q) = 3) ∧
      ¬ D ≤ normalizer (R : Set Janko4.Model) ∧ ¬ D ≤ E := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,hout,hnot⟩ :=
    normal_jankoFour_native_action h hH hgen c hY hescape hR C hC hRC e
  let R := ((residual H).subgroupOf Y).map f
  let E := (B.subgroupOf Y).map f
  have hES : (E : Set Janko4.Model) * (S : Set Janko4.Model) =
      (S : Set Janko4.Model) * (E : Set Janko4.Model) := by
    have hh := right_image_permutes c h.sylow_normalizes hH.1.1.2 hY.2 f
    change (E : Set Janko4.Model) *
      (((T : Subgroup G).subgroupOf Y).map f : Set Janko4.Model) =
      (((T : Subgroup G).subgroupOf Y).map f : Set Janko4.Model) * (E : Set Janko4.Model) at hh
    rw [←hS] at hh
    exact hh
  have hi := cubic_product_index S E hE hES
  obtain ⟨hi₂,hcore,homega,e₃,hqS,hqE⟩ := Janko4.cubic_sylow_quotient S E hE hi
  have hc : Nat.card (E ⊔ (S : Subgroup Janko4.Model) : Subgroup Janko4.Model) = 3 * 2^21 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup Janko4.Model) (S : Subgroup Janko4.Model)
      (E ⊔ (S : Subgroup Janko4.Model)) bot_le le_sup_right
    rw [relIndex_bot_left,relIndex_bot_left,hi,
      Janko4.OuterReduction.OddIndex.ambient_sylow_card S] at hh
    exact hh.symm.trans (Nat.mul_comm _ _)
  exact ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hc,hcore,jankoFour_local_five_extension S R hl hSR hfour,
    ⟨e₃,hqS,hqE⟩,hout,hnot⟩


private theorem two_kernel_of_residual_kernel
    {X Q : Type*} [Group X] [Finite X] [Group Q] (f : X →* Q)
    (hk : IsPGroup 2 (f.comp (pResidual 2 X).subtype).ker) : IsPGroup 2 f.ker := by
  let q := (QuotientGroup.mk' (pResidual 2 X)).comp f.ker.subtype
  let j : q.ker →* (f.comp (pResidual 2 X).subtype).ker :=
    { toFun := fun x => ⟨⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩,x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.val.val : X)) he))
  have hh := ((isPGroup_quotient_pResidual 2 (G := X)).to_subgroup ⊤).comap_of_ker_isPGroup
    q (hk.of_injective j hj)
  rw [comap_top] at hh
  exact hh.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup f.ker) ≃* f.ker)

/-- The literal original H/O₂(H), not just the residual section, is S₅ in
this normal J₄ branch. The action kernel is proved to be a two-group. -/
theorem normal_jankoFour_original_extension
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
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,hout,hnot⟩ :=
    normal_jankoFour_native_action h hH hgen c hY hescape hR C hC hRC e
  let R := ((residual H).subgroupOf Y).map f
  let N := R ⊔ (S : Subgroup Janko4.Model)
  have hHY : H ≤ Y := hY.2
  let fH := f.comp (inclusion hHY)
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  let i := (inclusion hHY).comp (pResidual 2 H).subtype
  have hiC (x : pResidual 2 H) : i x ∈ C :=
    hRC' (mem_map_of_mem H.subtype x.property)
  let j : pResidual 2 H →* C := i.codRestrict _ hiC
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => (z.val.val : G)) he))
  have hker : (fH.comp (pResidual 2 H).subtype).ker ≤ (pCore 2 C).comap j := by
    intro x hx
    have hz : e (QuotientGroup.mk' (pCore 2 C) (j x)) = 1 := by
      rw [←hf (j x)]
      exact hx
    change j x ∈ pCore 2 C
    exact (QuotientGroup.eq_one_iff _).mp (e.injective (hz.trans e.map_one.symm))
  have hk : IsPGroup 2 fH.ker := two_kernel_of_residual_kernel fH
    ((pCore_isPGroup.comap_of_injective j hj).to_le hker)
  have hN : fH.range = N := by
    change (f.comp (inclusion hHY)).range = N
    rw [MonoidHom.range_comp,inclusion_range hHY]
    have hg := congrArg (fun K : Subgroup G => (K.subgroupOf Y).map f)
      (residual_sup_sylow T H hH.1.1.2)
    rw [subgroupOf_sup hRY hTY,Subgroup.map_sup,←hS] at hg
    exact hg.symm
  let g := fH.rangeRestrict
  have hkg : IsPGroup 2 g.ker := by
    change IsPGroup 2 fH.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  let a := g.pCoreQuotientEquiv fH.rangeRestrict_surjective hkg
  let b := MulEquiv.subgroupCongr hN
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact ⟨a.trans (bq.trans (jankoFour_local_five_extension S R hl hSR hfour).some)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original sieve also recognizes the literal whole H/O₂(H) in its
normal J₄ row. Every preceding exclusion and the original component remain. -/
theorem localCartan_escape_seed_jankoFour_hall_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) →
          K = residual H ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          Nat.card B = 3 ∧
          Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5))) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,hJ4⟩ :=
    localCartan_escape_seed_jankoFour_section_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,?_⟩
  intro he
  obtain ⟨hKR,hfour,hB⟩ := hJ4 he
  let : C.Normal := hCn
  exact ⟨hKR,hfour,hB,LocalSieve.normal_jankoFour_original_extension
    h hH hgen c hY hescape (hKR ▸ hKL) C hC (hKR ▸ hKC) he.some⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
