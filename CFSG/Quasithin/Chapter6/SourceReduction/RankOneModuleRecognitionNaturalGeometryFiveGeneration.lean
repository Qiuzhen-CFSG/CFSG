module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryAmalgam
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalGeneration
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.ElementaryAbelian.Injective
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank

/-!
# The generation obstruction in the original contained S5 cover

Conjugation on a normal S5 section extends its specified quotient map
to a normalizing Sylow extension. Restrict automorphisms to the characteristic
A5 and use Aut(A5) = S5. The kernel is a two-group because its intersection
with the normal section is its two-core and its remaining quotient is a
two-group. The resulting map on KT has exactly O2(KT) as its kernel.

An actual elementary subgroup mapping onto a Sylow four-group of A5
contradicts generation one, by the proved elementary-lift obstruction for
E-members. Hence every even elementary image of the original cover has
order at most two in the contained S5 case. The original W/Z_S witness
and the Chapter12 application retain this stronger branch constraint.

Constructing a contradicting lift, or otherwise proving S5 escape, remains
with qt-d-1222-rankone-recognition-natural. So do mixed-amalgam recognition,
initial 6.1.4–5, omega escape and unconditional 6.1.27. No numerical lower
bound is inferred from a quotient model alone.

Source: Aschbacher–Smith 6.1.19, printed p.675, with E.1.1–6,
printed pp.209–211 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveGeneration
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private theorem exists_extension_action {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : (K ⧸ pCore 2 K) ≃* S5) :
    ∃ f : H →* S5, Function.Surjective f ∧
      ∀ k : K, f k = e (QuotientGroup.mk' (pCore 2 K) k) := by
  let a := normalQuotientAction K (pCore 2 K)
  let c : S5 ≃* MulAut A5 := MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let f : H →* S5 := c.symm.toMonoidHom.comp
    ((MulAut.characteristic A5).comp ((MulAut.congr e).toMonoidHom.comp a))
  have he (k : K) : f k = e (QuotientGroup.mk' (pCore 2 K) k) := by
    apply c.injective
    change c (c.symm _) = c _
    rw [c.apply_symm_apply]
    change (MulAut.characteristic A5) ((MulAut.congr e) (a k)) =
      MulAut.conjNormal (e (QuotientGroup.mk' (pCore 2 K) k))
    rw [normalQuotientAction_inner]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change e (QuotientGroup.mk' (pCore 2 K) k * e.symm x.val *
      (QuotientGroup.mk' (pCore 2 K) k)⁻¹) = _
    simp
  refine ⟨f,?_,he⟩
  intro x
  obtain ⟨k,hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) x
  exact ⟨k, (he k).trans hk⟩

private theorem not_generation_one_of_even_plane
    {H : Type*} [Group H] [Finite H]
    (f : H →* S5) (hf : Function.Surjective f)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : A.map f ≤ A5) (hc : Nat.card (A.map f) = 4) :
    ChapterE.generationParameter H ≠ 1 := by
  let D := (A.map f).subgroupOf A5
  have hp : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 A).map f |>.comap_subtype
  obtain ⟨Q,hDQ⟩ := hp.exists_le_sylow
  have hQcard : Nat.card Q = 4 := by
    rw [Q.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hDcard : Nat.card D = 4 := (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv).trans hc
  have hDeq : D = (Q : Subgroup A5) := eq_of_le_of_card_ge hDQ (by rw [hQcard,hDcard])
  have hmap : (Q : Subgroup A5).map (alternatingGroup (Fin 5)).subtype = A.map f := by
    rw [←hDeq,map_subgroupOf_eq_of_le hA]
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hA
  let : IsElementaryAbelian 2 Q := hDeq ▸ inferInstanceAs (IsElementaryAbelian 2 D)
  have hrank : 1 < Group.rank Q := by
    have hd := card_dvd_exponent_pow_rank' Q
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Q))
    have hl := Nat.le_of_dvd (by positivity : 0 < 2 ^ Group.rank Q) hd
    rw [hQcard] at hl
    by_contra hn
    have hu := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (Nat.le_of_not_gt hn)
    norm_num at hu
    omega
  let : Group.IsPerfect A5 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact LocalQuotientAction.not_generation_one_of_elementary_sylow_lift f hf A5
    (Group.IsPerfect.not_isSolvable A5) Q hrank
    (Theory.SpecificGroups.Alternating.FiveSylowMaximal.overgroup_le_sylow_normalizer Q)
    (Theory.SpecificGroups.Alternating.FiveSylowMaximal.sylow_normalizer_isCoatom Q).ne_top
    A hmap.symm


private theorem extension_kernel {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal] (e : (K ⧸ pCore 2 K) ≃* S5)
    (hquot : IsPGroup 2 (H ⧸ K)) (f : H →* S5) (hf : Function.Surjective f)
    (he : ∀ k : K, f k = e (QuotientGroup.mk' (pCore 2 K) k)) :
    f.ker = pCore 2 H := by
  let q := (QuotientGroup.mk' K).comp f.ker.subtype
  have hk : IsPGroup 2 q.ker := by
    let r : q.ker →* K := (f.ker.subtype.comp q.ker.subtype).codRestrict K (by
      intro x
      exact (QuotientGroup.eq_one_iff (N := K) x.val.val).mp x.property)
    have hr (x : q.ker) : r x ∈ pCore 2 K := by
      have hx : e (QuotientGroup.mk' (pCore 2 K) (r x)) = 1 :=
        (he (r x)).symm.trans x.val.property
      exact (QuotientGroup.eq_one_iff (N := pCore 2 K) (r x)).mp
        (e.injective (hx.trans e.map_one.symm))
    let r' : q.ker →* pCore 2 K := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : pCore 2 K => (a.val : H)) hxy
  have hfker : IsPGroup 2 f.ker := by
    have hh := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hk
    rw [comap_top] at hh
    exact hh.of_equiv topEquiv
  have hh := f.comap_pCore_of_ker_isPGroup hf hfker
  rwa [Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot,MonoidHom.comap_bot] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveGeneration

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]


/-- The full Sylow extension retains the specified S5 quotient of K,
including its exact two-core kernel and the restriction on every k in K. -/
theorem natural_five_sylow_extension_action
    (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5)) :
    ∃ f : (K ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5),
      Function.Surjective f ∧ f.ker = pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G) ∧
      ∀ k : K, f (inclusion le_sup_left k) = e (QuotientGroup.mk' (pCore 2 K) k) := by
  let H := K ⊔ (T : Subgroup G)
  have hKH : K ≤ H := le_sup_left
  let C := K.subgroupOf H
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let b : C ≃* K := subgroupOfEquivOfLe hKH
  let c : (C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  have hsup : C ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
    rw [←subgroupOf_sup hKH (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self]
  have hquot : IsPGroup 2 (H ⧸ C) := isPGroup_quotient_of_sup_eq_top C
    ((T : Subgroup G).subgroupOf H) T.isPGroup'.comap_subtype hsup
  obtain ⟨f,hf,he⟩ := NaturalFiveGeneration.exists_extension_action C c
  refine ⟨f,hf,NaturalFiveGeneration.extension_kernel C c hquot f hf he,?_⟩
  intro k
  have hh := he (b.symm k)
  change f (inclusion le_sup_left k) =
    e ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b))
      (QuotientGroup.mk' (pCore 2 C) (b.symm k))) at hh
  rw [QuotientGroup.congr_mk',b.apply_symm_apply] at hh
  exact hh

/-- The specified S5 quotient of a T-invariant subgroup extends to KT.
Generation one on KT therefore excludes an elementary even plane in K. -/
theorem natural_five_no_even_plane_of_generation_one
    (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : ChapterE.generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) = 1)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (A : Subgroup K) [IsElementaryAbelian 2 A]
    (hA : A.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤
      alternatingGroup (Fin 5)) :
    Nat.card (A.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) ≠ 4 := by
  intro hc
  obtain ⟨f,hf,_,he⟩ := natural_five_sylow_extension_action T K hTK e
  let B := A.map (inclusion (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left))
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hmap : B.map f = A.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
    rw [map_map]
    congr 1
    exact MonoidHom.ext he
  exact NaturalFiveGeneration.not_generation_one_of_even_plane f hf B
    (by rw [hmap]; exact hA) (by rw [hmap]; exact hc) hgen


/-- Every even elementary image in the original S5 quotient has order at
most two when the actual Sylow extension has generation parameter one. -/
theorem natural_five_even_elementary_image_card_le_two
    (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : ChapterE.generationParameter (K ⊔ (T : Subgroup G) : Subgroup G) = 1)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (A : Subgroup K) [IsElementaryAbelian 2 A]
    (hA : A.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤
      alternatingGroup (Fin 5)) :
    Nat.card (A.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) ≤ 2 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let D := (A.map q).subgroupOf (alternatingGroup (Fin 5))
  have hp : IsPGroup 2 D := (IsElementaryAbelian.isPGroup 2 A).map q |>.comap_subtype
  obtain ⟨Q,hDQ⟩ := hp.exists_le_sylow
  have hQcard : Nat.card Q = 4 := by
    rw [Q.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hDcard : Nat.card D = Nat.card (A.map q) :=
    Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv
  have hd := card_dvd_of_le hDQ
  rw [hQcard,hDcard] at hd
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  have hn := natural_five_no_even_plane_of_generation_one T K hTK hgen e A hA
  have hthree : Nat.card (A.map q) ≠ 3 := by
    intro hh
    rw [hh] at hd
    norm_num at hd
  change Nat.card (A.map q) ≠ 4 at hn
  change Nat.card (A.map q) ≤ 2
  omega

/-- The original invariant cover has no elementary lift of an even plane
under any of its literal S5 two-core markings. -/
@[expose] def NaturalFiveElementaryRestriction (P N : Subgroup G) : Prop :=
  let K := P ⊔ N.pCoreIn 2
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
    ∀ A : Subgroup K, IsElementaryAbelian 2 A →
      A.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ alternatingGroup (Fin 5) →
      Nat.card (A.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) ≤ 2

/-- In the contained S5 branch, the actual H-star generation hypothesis
forces the no-lift obstruction on the same original cover. -/
theorem natural_five_contained_elementary_restriction
    {X : Type*} [Group X] (T : Sylow 2 G) (P I N M : Subgroup G)
    (σ : I →* MulAut X) (hPI : P ≤ I)
    (hc : NaturalInvariantCoverData T P I N σ hPI)
    (hd : NaturalFiveContainedParabolicData T P N M) :
    NaturalFiveElementaryRestriction P N := by
  obtain ⟨_,_,hTK,_⟩ := hc
  obtain ⟨_,B,_,_,_,_,_,_,hgen⟩ := hd
  intro e A hA hEven
  let := hA
  exact natural_five_even_elementary_image_card_le_two T _ hTK hgen e A hEven

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The original W/Z_S witness gives the genuine escaping F.1.1 pair,
or a contained S5 parabolic whose original cover admits no elementary
even-plane lift. The quotient maps and all earlier premises are retained. -/
theorem exists_ambient_amalgam_or_five_no_lift
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveCubicParabolicData T L R P N ∧
            NaturalThreeInvariantParabolicData T L R P N M ∧
            (NaturalEscapingAmalgamData T L R P N M ∨
              (NaturalFiveContainedParabolicData T P N M ∧
                NaturalFiveElementaryRestriction P N)) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_contained_five h hnat hE hs hNS hab
  let := hZ
  let := hX
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,
    ham.imp_right (fun hd => ⟨hd,natural_five_contained_elementary_restriction
      T _ _ _ M σ hPI hcover hd⟩)⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
