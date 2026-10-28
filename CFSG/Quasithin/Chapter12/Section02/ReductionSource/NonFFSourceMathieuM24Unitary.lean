module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Quotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Five
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuOddControl
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuUnitaryCoordinates

/-!
# Excluding the unitary residual of the original M24 cocode parabolic

Assume the actual O²(H/O₂(H)) is PSU₃(4). The proved |V⁺|=4 and PSL₂(4)
marking of I⁺ construct its pair of Sylow centers, simultaneously position
them, and produce a five-torus in the image of H∩N_G(L). A coprime lift
inside that intersection normalizes V by TI, then normalizes I by its
literal quotient centralization. The previously proved cocode section
bound makes this same lifted subgroup centralize I and V.

Normalized odd-normalizer control (the Mathieu instance of 4.4.3 and
Remark 4.4.2, with its source premises and exceptions discharged) puts
N_G(X) in N_G(L). Thus I lies in N_G(L), contradicting the original H-star
minimality. No torus, coordinate, section-kernel or layer callback remains.
This proves the unitary branch exclusion, not the still-required full
E.2.2 quotient sieve or the final Mathieu-to-J4 theorem. The latter and
all other retained rows stay with qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith 8.2.9, printed p.720, and 4.4.2--3,
printed p.619, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.TrioCalculation
open ChapterE Chapter7.NormalizedSource
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.ParabolicReduction
open BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The concrete torus in the unitary branch belongs to the original local image. -/
theorem sourceOrbit_m24_unitary_quotient_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card F = 16) (hconj : ∀ x : F, J.conj x = x^4)
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ X : Subgroup (H ⧸ pCore 2 H), Nat.card X = 5 ∧
      X ≤ ((normalizer (L : Set G)).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) ∧
      X ≤ centralizer ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) := by
  have hVI : D.sourceOrbit ≤ I := s.generate ▸ le_sup_left
  have hVH : D.sourceOrbit ≤ H := hVI.trans s.family.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hVH
  let iH : H := inclusion s.family.le_ambient i
  have hgen : D.sourceOrbit.subgroupOf H ⊔ (D.sourceOrbit.subgroupOf H).map
      (MulAut.conj iH⁻¹).toMonoidHom = I.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVH,
      restricted_right_conjugate_image H D.sourceOrbit hVH iH,
      map_subgroupOf_eq_of_le s.family.le_ambient]
    exact s.generate
  obtain ⟨_,hfour,_⟩ := D.sourceOrbit_m24_pair_parabolic_quotient
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  obtain ⟨⟨b⟩,hIL⟩ := D.sourceOrbit_m24_pair_parabolic_residual
    h hmany hV hq hnon a E hE hg hAT s hUZ hH
  let Q := (I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  have hc4 : Nat.card (BenderSuzuki.PFAppendixIII.BinaryGaloisField 2) = 4 :=
    GaloisField.card 2 2 (by decide)
  let : IsSimpleGroup (BenderSuzuki.Converse.PSL2 (BenderSuzuki.PFAppendixIII.BinaryGaloisField 2)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hc4])
  let : IsSimpleGroup Q := b.isSimpleGroup
  let : Group.IsPerfect (BenderSuzuki.Converse.PSL2 (BenderSuzuki.PFAppendixIII.BinaryGaloisField 2)) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by rw [hc4]; decide)
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have hnot : ¬ IsPGroup 2 Q := fun hp => Group.IsPerfect.not_isNilpotent Q hp.isNilpotent
  exact MathieuUnitary.exists_quotient_five_of_pair J hJ hcard hconj e
    (T.subtype hH.1.1.2) ((normalizer (L : Set G)).subgroupOf H)
    (D.sourceOrbit.subgroupOf H) (I.subgroupOf H) iH i.property
    (fun _ hx => D.sourceOrbit_weakClosure_setup.le_sylow hx) hgen hfour hIL hnot
    (UnitaryExclusion.MarkedTorus.proper_overgroups_of_HStar T _ H hH)

/-- The unitary branch supplies an actual five-subgroup centralizing the original pair. -/
theorem sourceOrbit_m24_unitary_five_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card F = 16) (hconj : ∀ x : F, J.conj x = x^4)
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ X : Subgroup G, X ≤ H ∧ X ≤ normalizer (L : Set G) ∧ Nat.card X = 5 ∧
      X ≤ normalizer (D.sourceOrbit : Set G) ∧ X ≤ centralizer (I : Set G) := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
  let M := normalizer (L : Set G)
  have hVI : W ≤ I := s.generate ▸ le_sup_left
  have hVH : W ≤ H := hVI.trans s.family.le_ambient
  let iH : H := inclusion s.family.le_ambient i
  have hgen : W.subgroupOf H ⊔ (W.subgroupOf H).map
      (MulAut.conj iH⁻¹).toMonoidHom = I.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hVH,
      restricted_right_conjugate_image H W hVH iH,
      map_subgroupOf_eq_of_le s.family.le_ambient]
    exact s.generate
  have hTI := (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
  obtain ⟨_,hTU,_⟩ := D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many
    h hmany hV hq hnon a E hE hg hAT
  have hIC : I ≤ centralizer (U : Set G) := by
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s.intersection_central (hUZ.le hz)
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←selected_generates_hstar s hH]
    exact sup_le (hIC.trans (Subgroup.centralizer_le_normalizer _)) hTU
  have hUn : U ≠ ⊥ := by
    intro he
    exact s.intersection_ne_bot (hUZ.symm.trans he)
  obtain ⟨Z,hZ,hZM,hZC⟩ := D.sourceOrbit_m24_unitary_quotient_five
    h hmany hV hq hnon a E hE hg hAT s hUZ hH J hJ hcard hconj e
  obtain ⟨X₀,hX₀M,hX₀,hX₀Z⟩ := UnitaryExclusion.lift_five_subgroup (M.subgroupOf H) Z hZ hZM
  let X := X₀.map H.subtype
  have hXH : X ≤ H := map_subtype_le _
  have hXM : X ≤ M := by
    rintro _ ⟨x,hx,rfl⟩
    exact hX₀M hx
  have hX : Nat.card X = 5 := (card_map_of_injective H.subtype_injective).trans hX₀
  have hXV : X ≤ normalizer (W : Set G) :=
    (le_inf hXM (hXH.trans hHU)).trans
      (inf_normalizer_le_of_trivial_intersections hTI hUn (show U ≤ W from inf_le_left))
  have hX₀V : X₀ ≤ normalizer (W.subgroupOf H : Set H) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro w
    exact mem_normalizer_iff.mp (hXV (mem_map_of_mem H.subtype hx)) w.val
  have hTV : (T.subtype hH.1.1.2 : Subgroup H) ≤ normalizer (W.subgroupOf H : Set H) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro w
    exact mem_normalizer_iff.mp (D.sourceOrbit_weakClosure_setup.normalizes ht) w.val
  have hXC : X₀.map (QuotientGroup.mk' (pCore 2 H)) ≤
      centralizer ((I.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) :=
    hX₀Z ▸ hZC
  have hX₀I := UnitaryExclusion.normalizes_pair_of_quotient_centralization
    (T.subtype hH.1.1.2) (W.subgroupOf H) (I.subgroupOf H) X₀ iH i.property hTV hgen hX₀V hXC
  have hXI : X ≤ normalizer (I : Set G) := by
    have hm := (map_mono (f := H.subtype) hX₀I).trans (le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le s.family.le_ambient] at hm
  have hXsub : X.subgroupOf H = X₀ := comap_map_eq_self_of_injective H.subtype_injective X₀
  have hfix := D.sourceOrbit_m24_pair_five_centralizes
    h hmany hV hq hnon a E hE hg hAT s hUZ hHU X hXH hX hXI (by rw [hXsub]; exact hXC)
  exact ⟨X,hXH,hXM,hX,hXV,hfix.2⟩


/-- The original M24 cocode pair excludes the PSU₃(4) residual alternative in H/O₂(H). -/
theorem sourceOrbit_m24_unitary_residual_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card F = 16) (hconj : ∀ x : F, J.conj x = x^4)
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : False := by
  obtain ⟨X,_,hXM,hX,_,hXI⟩ := D.sourceOrbit_m24_unitary_five_centralizes
    h hmany hV hq hnon a E hE hg hAT s hUZ hH J hJ hcard hconj e
  have hne : X ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hX
    omega
  have hVI : D.sourceOrbit ≤ I := s.generate ▸ le_sup_left
  have hXW := hXI.trans (centralizer_le hVI)
  have hN := D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV
    (Or.inr (Or.inr (Or.inr hq))) hnon X hne (le_inf hXM hXW) (by rw [hX]; decide)
  have hIM : I ≤ normalizer (L : Set G) :=
    ((le_centralizer_iff.mp hXI).trans (Subgroup.centralizer_le_normalizer _)).trans hN
  apply hH.1.2
  rw [←selected_generates_hstar s hH]
  exact sup_le hIM D.sylow_normalizes_component

/-- The source unitary predicate, including arbitrary Hermitian forms, is excluded. -/
theorem sourceOrbit_m24_not_unitary_four_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S)
    (hUZ : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ ClassicalGroup.IsPSU (pResidual 2 (H ⧸ pCore 2 H)) 3 4 := by
  rintro ⟨F,hF,hFin,J,hcard,hconj,⟨e⟩⟩
  let := hF
  let := hFin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4)
    (by simpa [←Nat.card_eq_fintype_card] using hcard)
  have hfixed : Nat.card {x : F // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  obtain ⟨b⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J 4 hcard hfixed
  exact D.sourceOrbit_m24_unitary_residual_excluded h hmany hV hq hnon a E hE hg hAT
    s hUZ hH (HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
    rfl hcard hconj (e.trans b)


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
