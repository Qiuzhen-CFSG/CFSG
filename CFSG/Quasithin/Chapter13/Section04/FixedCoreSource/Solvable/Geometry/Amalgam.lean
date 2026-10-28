module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.LineParabolics
public import Theory.GroupTheory.NormalCharacteristicTwoCore

/-!
# Relative centralizers and exclusion of the product amalgam

Put P=IT and let B be the original inside parabolic L₂T. In any overgroup
X of P and B with nontrivial two-core, maximal two-locality and the two
parabolic maximalities give X∩M=B and X∩C_G(z)=P. The Sylow-residual
supplement then gives C_X(C_Z(O²(P)))=P. Since P/O₂(P)≅S₃, its
prime-to-three residual is its two-residual. The earlier fixed-line
identity for B gives the other relative centralizer and residual normality.
Thus the two normality clauses and the residual clause of13.4.7(c) hold
on the literal H₀=P∨B, conditional precisely on H₀∈H as in the source.

The product alternative13.4.7(1i) is excluded separately. Its commutator
bound would make M and H normalize O²(I). This is a nontrivial normal
subgroup of the characteristic-two group H, so its two-core is nontrivial.
Both groups normalize that core, contradicting maximal two-locality of M
and H≰M. The checked identity O²(IT)=O²(I) makes this the exact residual
bound in13.4.7, not a bound on a substituted subgroup.

Both endpoint theorems construct their local data from the original R₁
product. The literal L₂T application in OriginalAmalgam derives the generation
in M and the full fixed-subgroup centralizer from the earlier inside
parabolic and supplement data. It retains Z_L=C_Z(L), which need not
already equal C_V(L). Earlier-source discharge stays with
qt-d-1341-fixed-core-source. The remaining13.4.7(a–b)
applicability, H₀'s L₃(2) quotient, marked C₃ system and ambient fusion
remain with qt-d-1341-solvable-source. This does not prove full13.4.9.
Source: Aschbacher–Smith13.4.7 and13.4.9, printed pp.899 and906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem local_overgroup_le_maximal (M X : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hX : X ∈ Chapter1.H G) (hMX : M ≤ X) : X ≤ M := by
  have hn : X ≤ normalizer (X.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 X).le_normalizer_map X.subtype
  exact hn.trans (hM.2 ⟨X.pCoreIn 2,hX,isPGroup_pCoreIn 2 X,rfl⟩ (hMX.trans hn))

/-- The two literal intersections in every local overgroup of the source
amalgam. The assumption on X is exactly the conditional premise of13.4.7(c). -/
theorem amalgam_intersections_in_local_overgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : G) (P B X : Subgroup G)
    (hPH : P ≤ centralizer ({z} : Set G))
    (hPmax : IsCoatom (P.subgroupOf (centralizer ({z} : Set G))))
    (hPM : ¬ P ≤ normalizer (L : Set G))
    (hBM : B ≤ normalizer (L : Set G))
    (hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G))
    (hX : X ∈ Chapter1.H G) (hPX : P ≤ X) (hBX : B ≤ X) :
    X ⊓ normalizer (L : Set G) = B ∧ X ⊓ centralizer ({z} : Set G) = P := by
  let M := normalizer (L : Set G)
  let H := centralizer ({z} : Set G)
  have hmax : IsMaximalTwoLocal M :=
    (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
  have hMX : ¬ M ≤ X := fun hh => hPM (hPX.trans
    (local_overgroup_le_maximal M X hmax hX hh))
  have hXM : X.subgroupOf M ≠ ⊤ := by
    intro he
    apply hMX
    intro x hx
    exact (show (⟨x,hx⟩ : M) ∈ X.subgroupOf M from he ▸ mem_top _)
  have hb := (hBmax.le_iff_eq hXM).mp (subgroupOf_mono M hBX)
  have hXB : X ⊓ M = B := by
    have hh := congrArg (map M.subtype) hb
    rwa [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hBM] at hh
  have hHX : ¬ H ≤ X := by
    intro hh
    apply hMX
    change normalizer (L : Set G) ≤ X
    rw [←hgen]
    exact sup_le (inf_le_left.trans hh) hBX
  have hXH : X.subgroupOf H ≠ ⊤ := by
    intro he
    apply hHX
    intro x hx
    exact (show (⟨x,hx⟩ : H) ∈ X.subgroupOf H from he ▸ mem_top _)
  have hp := (hPmax.le_iff_eq hXH).mp (subgroupOf_mono H hPX)
  refine ⟨hXB,?_⟩
  have hh := congrArg (map H.subtype) hp
  rwa [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hPH] at hh

/-- A central Sylow involution belongs to the residual's fixed subgroup.
The residual and Sylow supplement centralize that subgroup, so the
relative fixed-subgroup centralizer is exactly the original parabolic. -/
theorem residual_fixed_centralizer_of_intersection
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P X : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hPX : P ≤ X)
    (hPH : P ≤ centralizer ({z} : Set G))
    (hinter : X ⊓ centralizer ({z} : Set G) = P) :
    let K := (pResidual 2 P).map P.subtype
    let ZK := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)
    X ⊓ centralizer (ZK : Set G) = P ∧
      (K.subgroupOf (X ⊓ centralizer (ZK : Set G))).Normal := by
  let K := (pResidual 2 P).map P.subtype
  let ZK := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)
  have hKP : K ≤ P := map_subtype_le _
  have hzK : z ∈ ZK := by
    refine ⟨hz,?_⟩
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hPH (hKP hk))
  have hgen : K ⊔ (T : Subgroup G) = P := by
    have hh := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTP))
    rwa [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP,
      ← MonoidHom.range_eq_map,range_subtype] at hh
  have hPC : P ≤ centralizer (ZK : Set G) := by
    rw [←hgen]
    refine sup_le (le_centralizer_iff.mpr inf_le_right) ?_
    intro t ht v hv
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hv.1).2.2 t ht).symm
  have he : X ⊓ centralizer (ZK : Set G) = P := by
    apply le_antisymm _ (le_inf hPX hPC)
    rw [←hinter]
    exact inf_le_inf_left X (centralizer_le (Set.singleton_subset_iff.mpr hzK))
  refine ⟨he,?_⟩
  rw [he]
  apply (normal_subgroupOf_iff_le_normalizer hKP).mpr
  simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
    (pResidual 2 P).le_normalizer_map P.subtype

private theorem twoThree_of_symmetric_three_quotient
    (A : Type*) [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : IsPiGroup twoThreePrimes A := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hcard : Nat.card A = 6 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),
      Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin,hn]
    rfl
  rw [IsPiGroup_iff]
  intro p hp
  rw [hcard] at hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp hp with hs | ht
  · rcases p.property.dvd_mul.mp (show p.val ∣ 2 * 3 from hs) with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow ht) |>.resolve_left p.property.ne_one)


/-- The literal two-residual is the prime-to-three residual of this
relative centralizer, as required by13.4.7(c). -/
theorem residual_fixed_cubic_centralizer_of_intersection
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P X : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hPX : P ≤ X)
    (hPH : P ≤ centralizer ({z} : Set G))
    (hinter : X ⊓ centralizer ({z} : Set G) = P)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) :
    let K := (pResidual 2 P).map P.subtype
    let C := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K : Set G) : Subgroup G) : Set G)
    C = P ∧ (K.subgroupOf C).Normal ∧ (primeToResidual 3 C).map C.subtype = K := by
  obtain ⟨he,hn⟩ := residual_fixed_centralizer_of_intersection z hz P X hTP hPX hPH hinter
  refine ⟨he,hn,?_⟩
  rw [he,←twoResidual_eq_primeToResidual_three (twoThree_of_symmetric_three_quotient P eP)]

/-- Both relative normality clauses and the prime-to-three residual clause
in13.4.7(c), using the original fixed line for the inside parabolic. -/
theorem amalgam_residual_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P B X : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (hPH : P ≤ centralizer ({z} : Set G))
    (hPmax : IsCoatom (P.subgroupOf (centralizer ({z} : Set G))))
    (hPM : ¬ P ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (hBM : B ≤ normalizer (L : Set G))
    (hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G))
    (hfixed : centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 B).map B.subtype : Set G) : Subgroup G) : Set G) =
        normalizer (L : Set G))
    (hX : X ∈ Chapter1.H G) (hPX : P ≤ X) (hBX : B ≤ X) :
    let K₁ := (pResidual 2 P).map P.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    let C₁ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₁ : Set G) : Subgroup G) : Set G)
    let C₂ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₂ : Set G) : Subgroup G) : Set G)
    X ⊓ normalizer (L : Set G) = B ∧ X ⊓ centralizer ({z} : Set G) = P ∧
      C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
      (primeToResidual 3 C₁).map C₁.subtype = K₁ := by
  obtain ⟨hXM,hXH⟩ := amalgam_intersections_in_local_overgroup h structural z P B X
    hPH hPmax hPM hBM hBmax hgen hX hPX hBX
  obtain ⟨hC₁,hn₁,hr⟩ := residual_fixed_cubic_centralizer_of_intersection z hz P X
    hTP hPX hPH hXH eP
  have hC₂ : X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 B).map B.subtype : Set G) : Subgroup G) : Set G) = B := by
    rw [hfixed]
    exact hXM
  refine ⟨hXM,hXH,hC₁,hC₂,hn₁,?_,hr⟩
  rw [hC₂]
  apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mpr
  simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
    (pResidual 2 B).le_normalizer_map B.subtype

theorem original_R1_amalgam_centralizers
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G))
    (hBmax : IsCoatom (B.subgroupOf (normalizer (L : Set G))))
    (hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G))
    (hfixed : centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 B).map B.subtype : Set G) : Subgroup G) : Set G) =
        normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let X := P ⊔ B
    X ∈ Chapter1.H G →
    let K₁ := (pResidual 2 P).map P.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    let C₁ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₁ : Set G) : Subgroup G) : Set G)
    let C₂ := X ⊓ centralizer ((omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (K₂ : Set G) : Subgroup G) : Set G)
    X ⊓ normalizer (L : Set G) = B ∧ X ⊓ H = P ∧
      C₁ = P ∧ C₂ = B ∧ (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
      (primeToResidual 3 C₁).map C₁.subtype = K₁ := by
  dsimp only
  intro hX
  obtain ⟨_,hp,⟨eP⟩,hstar⟩ := original_R1_line_parabolics
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hTH := original_sylow_le_centralizer hz
  have hRT := (firstFlagCore_local_data h structural D m z hz hzL).1
  have hIH : conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m))
      (centralizer ({z.val} : Set G)) ≤ centralizer ({z.val} : Set G) := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  exact amalgam_residual_centralizers h structural z.val hz _ B _
    le_sup_right (sup_le hIH hTH) hp.right_maximal hstar.1.2 eP
    hBM hBmax hgen hfixed hX le_sup_left le_sup_right

private theorem not_two_group_of_symmetricThree_quotient
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) : ¬ IsPGroup 2 A := by
  intro hp
  obtain ⟨n,hn⟩ := ((hp.to_quotient (pCore 2 A)).of_equiv e).exists_card_eq
  have hd : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]
  rw [hn] at hd
  exact (by decide : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The source product alternative13.4.7(1i) is impossible: its residual
commutator bound would make M and H normalize the same nontrivial two-core. -/
theorem thompson_residual_not_commuting_with_inside_residual
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    {z : G} (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hquot :
      let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hTB : (T : Subgroup G) ≤ B)
    (hgen : (centralizer ({z} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    let K := (pResidual 2 I).map I.subtype
    ¬ ⁅K,(pResidual 2 B).map B.subtype⁆ ≤ K.pCoreIn 2 := by
  let H := centralizer ({z} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let K := (pResidual 2 I).map I.subtype
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  have hKI : K ≤ I := map_subtype_le _
  have hKH : K ≤ H := hKI.trans hIH
  have hnH : H ≤ normalizer (K : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hKne : K ≠ ⊥ := by
    intro hb
    have hr : pResidual 2 I = ⊥ := (map_eq_bot_iff_of_injective _ I.subtype_injective).mp hb
    have hp := isPGroup_quotient_pResidual (G := I) 2
    obtain ⟨eI⟩ := hquot
    exact not_two_group_of_symmetricThree_quotient eI (hp.of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot))
  let N := K.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hnH
  have hn : N ≠ ⊥ := by
    intro hb
    apply hKne
    change K.subgroupOf H = ⊥ at hb
    rw [←map_subgroupOf_eq_of_le hKH,hb,Subgroup.map_bot]
  have hHchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T)
      (centralizer_mem_HOver hz hz1))
  have hcore : K.pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hk : pCore 2 K = ⊥ := (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hb
    let e := subgroupOfEquivOfLe hKH
    apply twoCore_ne_bot_of_normal_of_centralizer_le N hHchar hn
    apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
    rw [pCore_map_iso 2 e,hk]
  change ¬ ⁅K,(pResidual 2 B).map B.subtype⁆ ≤ K.pCoreIn 2
  intro hcomm
  have hBN : (pResidual 2 B).map B.subtype ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 K))
  have hBT : B ≤ normalizer (K : Set G) := by
    have hb := congrArg (map B.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTB))
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTB,
      ← MonoidHom.range_eq_map,range_subtype] at hb
    rw [←hb]
    exact sup_le hBN (hTH.trans hnH)
  have hMN : normalizer (L : Set G) ≤ normalizer (K : Set G) := by
    rw [←hgen]
    exact sup_le (inf_le_left.trans hnH) hBT
  have hchar := normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hmax := (h.source_normalizer_maximal_unique structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
  have hNM : normalizer (K.pCoreIn 2 : Set G) ≤ normalizer (L : Set G) :=
    hmax.2 ⟨K.pCoreIn 2,hcore,isPGroup_pCoreIn 2 K,rfl⟩ (hMN.trans hchar)
  exact hout (hnH.trans (hchar.trans hNM))

theorem original_R1_excludes_amalgam_product
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (B : Subgroup G) (hTB : (T : Subgroup G) ≤ B)
    (hgen : (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)) ⊔ B =
      normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let P := I ⊔ (T : Subgroup G)
    let K₁ := (pResidual 2 P).map P.subtype
    let K₂ := (pResidual 2 B).map B.subtype
    ¬ ⁅K₁,K₂⁆ ≤ K₁.pCoreIn 2 := by
  obtain ⟨_,_,hI,_,_,_,_,_,_⟩ := centralizer_pair_quotient_of_original_R1
    h₀ h structural D m hcase z hz hzL hVJ hout hfusion h1339 hsolv hindex h1342
  have hRT := (firstFlagCore_local_data h structural D m z hz hzL).1
  dsimp only
  rw [thompson_sylow_join_residual hz (firstFlagCore h structural D m) hRT]
  exact thompson_residual_not_commuting_with_inside_residual h₀ h structural hz
    (fun he => hzL (he ▸ one_mem _)) (firstFlagCore h structural D m) hRT hI hout B hTB hgen

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
