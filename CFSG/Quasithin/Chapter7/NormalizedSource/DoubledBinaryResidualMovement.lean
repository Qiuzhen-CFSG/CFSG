module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPushingUp
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.SpecificGroups.SymmetricThree.CubicSelection
public import Theory.GroupTheory.CComponent.NormalFromNontrivialImage

/-!
# Movement by the original component Sylow in the reduced quotient

The two-core of the residual/Sylow base is its Sylow intersection with
C(L₀/O₂(L₀)). If the component Sylow were contained in that core, it
would make Q Sylow in the component join. Thus a component surviving
the rank-one block exclusions moves L₀ modulo its two-core.

The same assertion holds in the literal reduced-action quotient. The
paired-plane S₃ quotient factors through its local-base image, and its
Sylow kernel is precisely Q. This identifies the image base's two-core
without assuming that the full reduced-action kernel is a two-group.
The original residual has cubic quotient over its two-core. A normal
intersection outside that core therefore contains the whole two-perfect
residual. Its noncentral image prevents any Sylow exchange of the component
image. Normality then lifts through the unrestricted full action kernel.
The Chapter12 ResidualMovement consumer supplies the original maps.
Source: Aschbacher–Smith 7.7.9(2) and 7.7.10, printed p.708, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualMovement
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

private theorem sylow_sectionCentralizer (P : Sylow 2 G) (A : Subgroup G)
    (hp : IsPPerfect 2 A) (hPA : (P : Subgroup G) ≤ normalizer (A : Set G)) :
    (P : Subgroup G) ⊓ twoSectionCentralizer A (normalizer (A : Set G)) =
      (A ⊔ (P : Subgroup G)).pCoreIn 2 := by
  let Z := twoSectionCentralizer A (normalizer (A : Set G))
  obtain ⟨S,hS⟩ := sylow_core_sectionCentralizer P A hp hPA
  have hQP : (A ⊔ (P : Subgroup G)).pCoreIn 2 ≤ (P : Subgroup G) := by
    have hh := pCoreIn_le_sylow _ (P.subtype (show (P : Subgroup G) ≤ A ⊔ (P : Subgroup G) from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (P : Subgroup G) ≤ A ⊔ (P : Subgroup G) from le_sup_right)] using hh
  have hSP : (S : Subgroup Z) ≤ (P : Subgroup G).subgroupOf Z := by
    intro s hs
    exact hQP (hS ▸ mem_map_of_mem Z.subtype hs)
  have he := S.is_maximal' P.isPGroup'.comap_subtype hSP
  have hh := congrArg (map Z.subtype) he
  change ((P : Subgroup G).subgroupOf Z).map Z.subtype = (S : Subgroup Z).map Z.subtype at hh
  rw [subgroupOf_map_subtype,hS] at hh
  exact hh

theorem component_sylow_not_le_core (P : Sylow 2 G) (C Q : Subgroup G)
    (hC : C.IsSubnormal) (hQ : IsPGroup 2 Q)
    (hQC : Q ≤ normalizer (C : Set G))
    (hnot : ¬ Chapter1.IsSylowIn 2 Q (C ⊔ Q)) :
    ¬ (P : Subgroup G) ⊓ C ≤ Q := by
  intro hh
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_subnormal C hC
  apply hnot
  apply hQ.exists_sylow_sup_of_coprime_index C Q hQC (S : Subgroup C) S.not_dvd_index
  rw [hS,subgroupOf_map_subtype]
  exact hh

theorem component_sylow_moves_residual (P : Sylow 2 G) (A C Q : Subgroup G)
    (hA : IsPPerfect 2 A) (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hcore : (A ⊔ (P : Subgroup G)).pCoreIn 2 = Q)
    (hC : C.IsSubnormal) (hQ : IsPGroup 2 Q)
    (hQC : Q ≤ normalizer (C : Set G))
    (hnot : ¬ Chapter1.IsSylowIn 2 Q (C ⊔ Q)) :
    ¬ ⁅A,(P : Subgroup G) ⊓ C⁆ ≤ A.pCoreIn 2 := by
  intro hh
  apply component_sylow_not_le_core P C Q hC hQ hQC hnot
  have hsect : (P : Subgroup G) ⊓ C ≤ twoSectionCentralizer A (normalizer (A : Set G)) :=
    (le_twoSectionCentralizer_iff _ _ _).mpr ⟨inf_le_left.trans hPA,inf_le_left.trans hPA,hh⟩
  exact (le_inf inf_le_left hsect).trans_eq ((sylow_sectionCentralizer P A hA hPA).trans hcore)

/-- A larger action quotient retains the local core when the Sylow kernel
is already the original core and the smaller action has trivial two-core. -/
theorem local_core_image {D R : Type*} [Group D] [Finite D] [Group R]
    (P : Sylow 2 G) (A Q : Subgroup G)
    (hQ : (A ⊔ (P : Subgroup G)).pCoreIn 2 = Q)
    (π : (A ⊔ (P : Subgroup G) : Subgroup G) →* R)
    (hπ : Function.Surjective π) (hR : pCore 2 R = ⊥)
    (hker : ∀ p (hp : p ∈ (P : Subgroup G)),
      π ⟨p,mem_sup_right hp⟩ = 1 → p ∈ Q)
    (q : G →* D) (hq : Function.Surjective q)
    (hfactor : q.ker.subgroupOf (A ⊔ (P : Subgroup G)) ≤ π.ker) :
    ((A ⊔ (P : Subgroup G)).map q).pCoreIn 2 = Q.map q := by
  let B := A ⊔ (P : Subgroup G)
  let B' := B.map q
  let r := q.subgroupMap B
  have hr : Function.Surjective r := q.subgroupMap_surjective B
  have hk : r.ker ≤ π.ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hfactor
  let f : B' →* R := MonoidHom.liftOfSurjective r hr ⟨π,hk⟩
  have hf (x : B) : f (r x) = π x := by simp [f]
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨b,rfl⟩ := hπ z
    exact ⟨r b,hf b⟩
  have hcoreker : pCore 2 B' ≤ f.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    apply le_bot_iff.mp
    rw [←hR]
    exact le_sSup ⟨(inferInstance : (pCore 2 B').Normal).map f hfs,pCore_isPGroup.map f⟩
  let P' := P.mapSurjective hq
  have hPB : (P' : Subgroup D) ≤ B' := map_mono le_sup_right
  have hcoreP : B'.pCoreIn 2 ≤ (P' : Subgroup D) := by
    have hh := pCoreIn_le_sylow B' (P'.subtype hPB)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPB] using hh
  apply le_antisymm
  · intro x hx
    obtain ⟨p,hp,he⟩ := hcoreP hx
    have hb : (⟨x,pCoreIn_le 2 B' hx⟩ : B') ∈ pCore 2 B' := by
      rcases hx with ⟨b,hb,rfl⟩
      exact hb
    have he' : r ⟨p,mem_sup_right hp⟩ = ⟨x,pCoreIn_le 2 B' hx⟩ := Subtype.ext he
    have hz : π ⟨p,mem_sup_right hp⟩ = 1 := by
      rw [←hf,he']
      exact hcoreker hb
    exact ⟨p,hker p hp hz,he⟩
  · rw [←hQ]
    change ((pCore 2 B).map B.subtype).map q ≤ (pCore 2 B').map B'.subtype
    rw [map_map]
    have hm : (pCore 2 B).map r ≤ pCore 2 B' :=
      le_sSup ⟨(inferInstance : (pCore 2 B).Normal).map r hr,pCore_isPGroup.map r⟩
    have hh := map_mono (f := B'.subtype) hm
    rw [map_map] at hh
    exact hh

omit [Finite G] in
private theorem component_sylow_image_not_le_core {D : Type*} [Group D]
    (P : Sylow 2 G) (C Q : Subgroup G)
    (hQP : Q ≤ (P : Subgroup G))
    (hnot : ¬ (P : Subgroup G) ⊓ C ≤ Q)
    (q : G →* D) (hker : (P : Subgroup G) ⊓ q.ker ≤ Q) :
    ¬ (P : Subgroup G).map q ⊓ C.map q ≤ Q.map q := by
  intro hh
  apply hnot
  intro p hp
  obtain ⟨r,hr,he⟩ := hh ⟨mem_map_of_mem q hp.1,mem_map_of_mem q hp.2⟩
  have hk : p*r⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
  have hpr : p*r⁻¹ ∈ Q := hker ⟨P.mul_mem hp.1 (P.inv_mem (hQP hr)),hk⟩
  simpa only [inv_mul_cancel_right] using Q.mul_mem hpr hr

/-- The original component Sylow still moves the residual modulo its
intrinsic two-core in any quotient retaining the local core. -/
theorem component_sylow_moves_quotient {D : Type*} [Group D] [Finite D]
    (P : Sylow 2 G) (A C Q : Subgroup G)
    (hA : IsPPerfect 2 A) (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hQP : Q ≤ (P : Subgroup G))
    (hnot : ¬ (P : Subgroup G) ⊓ C ≤ Q)
    (q : G →* D) (hq : Function.Surjective q)
    (hker : (P : Subgroup G) ⊓ q.ker ≤ Q)
    (hcore : ((A ⊔ (P : Subgroup G)).map q).pCoreIn 2 = Q.map q) :
    ¬ ⁅A.map q,(P : Subgroup G).map q ⊓ C.map q⁆ ≤ (A.map q).pCoreIn 2 := by
  let P' := P.mapSurjective hq
  have hnorm : (P' : Subgroup D) ≤ normalizer (A.map q : Set D) :=
    (map_mono hPA).trans (A.le_normalizer_map q)
  have hp : IsPPerfect 2 (A.map q) := hA.of_surjective
    (q.subgroupMap A) (q.subgroupMap_surjective A)
  intro hc
  have hsect := (le_twoSectionCentralizer_iff (A.map q) (normalizer (A.map q : Set D))
    ((P' : Subgroup D) ⊓ C.map q)).mpr ⟨inf_le_left.trans hnorm,inf_le_left.trans hnorm,hc⟩
  have hh := (le_inf inf_le_left hsect).trans_eq (sylow_sectionCentralizer P' (A.map q) hp hnorm)
  change (P : Subgroup G).map q ⊓ C.map q ≤ (A.map q ⊔ (P : Subgroup G).map q).pCoreIn 2 at hh
  rw [←Subgroup.map_sup,hcore] at hh
  exact component_sylow_image_not_le_core P C Q hQP hnot q hker hh

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
open ChapterE BinaryLinearThree DoubledBinaryPlanes DoubledBinaryPlaneQuotient DoubledBinaryLocalCore

omit [Finite G] in
/-- The original local base, rather than an arbitrary plane normalizer,
induces the full paired-plane S₃ action. -/
theorem localBase_quotient
    (W L B : Subgroup G) [IsElementaryAbelian 2 W]
    (hLN : L ≤ normalizer (W : Set G))
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (E : Additive W ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ l w, E (automizerRepresentation W
      (W.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) =
        NaturalDual.action (q l) (E w))
    (a : Automizer W ≃* MulAut BinaryLinearThree.Group)
    (ha : ∀ l, a (W.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hcov : ∀ b g w, E (automizerRepresentation W b (E.symm (NaturalDual.action g (E w)))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W b w)))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hBN : B ≤ normalizer (W : Set G))
    (hBC : B ≤ centralizer (ambientPlane W E v f : Set G))
    (hLB : L ⊓ centralizer (ambientPlane W E v f : Set G) ≤ B) :
    ∃ π : B →* Equiv.Perm (Fin 3), Function.Surjective π ∧
      π.ker = (centralizer (W : Set G)).subgroupOf B := by
  let U := ambientPlane W E v f
  let I := inducedAutomizer W (centralizer (U : Set G))
  let b : B →* Automizer W := W.normalizerMonoidHom.rangeRestrict.comp (inclusion hBN)
  let r : B →* I := b.codRestrict I (fun x => ⟨inclusion hBN x,hBC x.property,rfl⟩)
  have hr : Function.Surjective r := by
    intro x
    have hx := (component_centralizer_image W L hLN q hq E a ha hcov v f hfv).ge x.property
    obtain ⟨n,hn,he⟩ := hx
    exact ⟨⟨n,hLB hn⟩,Subtype.ext he⟩
  obtain ⟨e⟩ := ambientPlane_equiv W L hLN q hq E hE a ha hcov v f hfv
  refine ⟨e.toMonoidHom.comp r,e.surjective.comp hr,?_⟩
  ext x
  change e (r x) = 1 ↔ (x : G) ∈ centralizer (W : Set G)
  rw [←e.map_one,e.injective.eq_iff]
  have he : r x = 1 ↔ W.normalizerMonoidHom (inclusion hBN x) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun z : I => z.val.val) hh
    · intro hh
      exact Subtype.ext (Subtype.ext hh)
  rw [he]
  change inclusion hBN x ∈ W.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl


/-- A symmetric-three quotient with two-group kernel gives a cubic
quotient of the two-residual by its intrinsic two-core. -/
theorem residual_cubic_quotient (f : G →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nat.card ((pResidual 2 G) ⧸ pCore 2 (pResidual 2 G)) = 3 := by
  let A := pResidual 2 G
  let r := f.subgroupMap A
  have hr : Function.Surjective r := f.subgroupMap_surjective A
  have he : A.map f = alternatingGroup (Fin 3) :=
    (map_pResidual_of_surjective 2 f hf).trans
      Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_eq
  have hc : Nat.card (A.map f) = 3 := by
    rw [he,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hp3 : IsPGroup 3 (A.map f) := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hcore : pCore 2 (A.map f) = ⊥ := by
    have hdis := IsPGroup.disjoint_of_coprime
      (pCore_isPGroup (p := 2) (G := A.map f))
      (hp3.to_subgroup (pCore 2 (A.map f))) (by decide : Nat.Coprime 2 3)
    exact disjoint_self.mp hdis
  have hkr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hke : r.ker = pCore 2 A := by
    have hh := r.comap_pCore_of_ker_isPGroup hr hkr
    rw [hcore] at hh
    exact hh
  rw [←hke]
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hr).toEquiv).trans hc

/-- Nontrivial section movement forces a two-perfect cubic residual
into the normalized component. -/
theorem residual_le_component_of_cubic_quotient (A C S : Subgroup G)
    (hA : IsPPerfect 2 A) (hAC : A ≤ normalizer (C : Set G))
    (hSA : S ≤ normalizer (A : Set G)) (hSC : S ≤ C)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hmove : ¬ ⁅A,S⁆ ≤ A.pCoreIn 2) : A ≤ C := by
  let N := C.subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer hAC
  let q := QuotientGroup.mk' (pCore 2 A)
  have hNnot : ¬ N ≤ pCore 2 A := by
    intro hh
    apply hmove
    have hcomm : ⁅A,S⁆ ≤ A ⊓ C := le_inf
      (le_normalizer_iff_commutator_le_left.mp hSA)
      ((commutator_mono le_rfl hSC).trans
        (le_normalizer_iff_commutator_le_right.mp hAC))
    intro x hx
    exact mem_map_of_mem A.subtype (hh (show (⟨x,(hcomm hx).1⟩ : A) ∈ N from (hcomm hx).2))
  have hne : N.map q ≠ ⊥ := by
    intro hh
    apply hNnot
    have hk := (Subgroup.map_eq_bot_iff _).mp hh
    simpa only [q,QuotientGroup.ker_mk'] using hk
  have htop : N.map q = ⊤ := by
    have hd : Nat.card (N.map q) ∣ 3 := hc ▸ (N.map q).card_subgroup_dvd_card
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hd | hd
    · exact (hne (card_eq_one.mp hd)).elim
    · apply eq_of_le_of_card_ge le_top
      simp only [card_top,hc,hd,le_refl]
  have hs : N ⊔ pCore 2 A = ⊤ := by
    have hh := congrArg (comap q) htop
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
  have hp : IsPGroup 2 (A ⧸ N) := isPGroup_quotient_of_sup_eq_top N (pCore 2 A)
    pCore_isPGroup hs
  have hn : pResidual 2 A ≤ N := sInf_le ⟨inferInstance,hp⟩
  rw [(pResidual_eq_top_iff 2 A).mpr hA] at hn
  intro a ha
  exact hn (mem_top (⟨a,ha⟩ : A))


omit [Finite G] in
private theorem normalizer_le_component_normalizer
    (A C : Subgroup G) (hC : IsComponent G C)
    (hAC : A ≤ C) (hne : ¬ A ≤ centralizer (C : Set G)) :
    normalizer (A : Set G) ≤ normalizer (C : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hh
  have hc := hC.commutator_eq_bot_of_ne (hC.map_conj g) (Ne.symm hh)
  have hconj : A ≤ C.map (MulAut.conj g).toMonoidHom := by
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hAC
    have he : A.map (MulAut.conj g).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hg
    rwa [he] at hm
  exact hne (hconj.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)))

/-- A contained residual whose image moves the component Sylow prevents
Sylow exchange, so a Sylow-supplemented lifted component is normal. -/
theorem component_normal_of_residual_movement {D : Type*} [_root_.Group D]
    (P : Sylow 2 G) (A C : Subgroup G) (hC : C.IsCComponent)
    (hAC : A ≤ C) (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hgen : C ⊔ (P : Subgroup G) = ⊤)
    (q : G →* D) (hq : Function.Surjective q) (hc : IsComponent D (C.map q))
    (hmove : ¬ ⁅A.map q,(P : Subgroup G).map q ⊓ C.map q⁆ ≤ (A.map q).pCoreIn 2) :
    C.Normal := by
  have hn : ¬ A.map q ≤ centralizer (C.map q : Set D) := by
    intro hh
    apply hmove
    have hzero : ⁅A.map q,(P : Subgroup G).map q ⊓ C.map q⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hh.trans (centralizer_le inf_le_right))
    rw [hzero]
    exact bot_le
  have hPN : (P : Subgroup G).map q ≤ normalizer (C.map q : Set D) :=
    ((map_mono hPA).trans (A.le_normalizer_map q)).trans
      (normalizer_le_component_normalizer (A.map q) (C.map q) hc (map_mono hAC) hn)
  have ht : C.map q ⊔ (P : Subgroup G).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q hq]
  have hnorm : (C.map q).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←ht]
    exact sup_le (C.map q).le_normalizer hPN))
  have hne : C.map q ≠ ⊥ := by
    intro he
    apply hmove
    rw [he,inf_bot_eq,commutator_bot_right]
    exact bot_le
  exact hC.normal_of_normal_nontrivial_image q hnorm hne

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualMovement
