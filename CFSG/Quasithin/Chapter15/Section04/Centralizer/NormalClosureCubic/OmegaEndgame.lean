module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.NormalClosureCubic
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Normalizers
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.SmallFittingResidual
public import Theory.ElementaryAbelian.Quotient

/-!
# The second-overgroup omega endgame in 15.4.8

The actual image maps identify the two images of the source normal closure
with its intrinsic quotient by O₂. In the second action centralizer, its
normal cubic factors centralize O₃. The three-rank bound therefore makes
their elementary nine-group exactly Ω₁(O₃). Characteristicness and residual
recovery lift normality to the second maximal two-local overgroup. The two
overgroups then normalize the same nontrivial two-core and must coincide.

Source: Aschbacher--Smith, final paragraph of 15.4.8, printed p.1160.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.OmegaEndgame
open FamilySource LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G]

/-- The literal action centralizer is relatively normal in its overgroup. -/
theorem actionCentralizer_normalizes (T M : Subgroup G) :
    M ≤ normalizer ((M ⊓ centralizer (localV T M : Set G) : Subgroup G) : Set G) := by
  let W := normalClosure ((Stellmacher.omegaOneCenterAmbient T).subgroupOf M : Set M)
  have he : (M ⊓ centralizer (localV T M : Set G)).subgroupOf M = centralizer (W : Set M) := by
    ext x
    constructor
    · intro hx w hw
      apply Subtype.ext
      exact hx.2 w (mem_map_of_mem M.subtype hw)
    · intro hx
      refine ⟨x.property, ?_⟩
      rintro z ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (hx w hw)
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
  rw [he]
  infer_instance

/-- Relative normality through the two actual overgroups gives the core
containment needed for the source quotient map. -/
theorem core_le_of_action_control (T : Sylow 2 G) (Z M D : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTM : (T : Subgroup G) ≤ M)
    (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hD : D ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hc : D ≤ M ⊓ centralizer (localV (T : Subgroup G) M : Set G)) :
    D.pCoreIn 2 ≤ M.pCoreIn 2 := by
  have hn : M ⊓ centralizer (localV (T : Subgroup G) M : Set G) ≤ normalizer (D : Set G) :=
    (inf_le_right.trans (action_centralizer_le T Z M hZT hTM hZ)).trans hD.2.2
  have hDH : D.pCoreIn 2 ≤ (M ⊓ centralizer (localV (T : Subgroup G) M : Set G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (p := 2) (Y := D)
      (L := M ⊓ centralizer (localV (T : Subgroup G) M : Set G)) hc hn
  have hHM : (M ⊓ centralizer (localV (T : Subgroup G) M : Set G)).pCoreIn 2 ≤ M.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (p := 2)
      (Y := M ⊓ centralizer (localV (T : Subgroup G) M : Set G)) (L := M)
      inf_le_left (actionCentralizer_normalizes (T : Subgroup G) M)
  exact hDH.trans hHM

/-- The quotient equivalence retains the original map from Y into M/O₂(M).
The sole core premise is a literal subgroup containment, supplied by source
relative normality in the actual action centralizer. -/
theorem coreQuotientEquivImage (M Y : Subgroup G) (hYM : Y ≤ M)
    (hcore : Y.pCoreIn 2 ≤ M.pCoreIn 2) :
    ∃ e : Y ⧸ pCore 2 Y ≃* image M Y,
      ∀ y : Y, (e (QuotientGroup.mk' (pCore 2 Y) y) : CoreQuotient M) =
        quotientMap M ⟨(y : G), hYM y.property⟩ := by
  let f : Y →* image M Y :=
    ((quotientMap M).subgroupMap (Y.subgroupOf M)).comp
      (subgroupOfEquivOfLe hYM).symm.toMonoidHom
  have hf : Function.Surjective f := (quotientMap M).subgroupMap_surjective _ |>.comp
    (subgroupOfEquivOfLe hYM).symm.surjective
  have hk : f.ker = pCore 2 Y := by
    apply le_antisymm
    · have he : f.ker = (pCore 2 M).comap (inclusion hYM) := by
        ext y
        change (f y = 1) ↔ _
        rw [Subtype.ext_iff]
        exact QuotientGroup.eq_one_iff (N := pCore 2 M) _
      rw [he]
      exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective _
        (inclusion_injective hYM)⟩
    · intro y hy
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change quotientMap M ⟨(y : G), hYM y.property⟩ = 1
      apply (QuotientGroup.eq_one_iff (N := pCore 2 M) _).mpr
      obtain ⟨m, hm, he⟩ := hcore (mem_map_of_mem Y.subtype hy)
      exact (Subtype.ext he : m = ⟨(y : G), hYM y.property⟩) ▸ hm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), fun y => rfl⟩

variable [Finite G]

/-- Three-rank descends through this two-core quotient by lifting elementary
subgroups across its coprime kernel. -/
theorem three_rank_quotient_le (M : Subgroup G) (hr : primeRank 3 M ≤ 2) :
    primeRank 3 (CoreQuotient M) ≤ 2 := by
  have hk : Nat.Coprime 3 (Nat.card (quotientMap M).ker) := by
    rw [quotientMap, QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  apply (primeRank_le_iff_elementary_card_le (CoreQuotient M)).mpr
  intro E hE
  let := hE
  obtain ⟨A, hA, _, hcard⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    (quotientMap M) (QuotientGroup.mk'_surjective _) hk E
  rw [← hcard]
  exact (primeRank_le_iff_elementary_card_le M).mp hr A hA

end CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.OmegaEndgame


public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.OmegaEndgame
open FamilySource LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]

private theorem core_centralizes_normal_cubic (A : Subgroup G) [A.Normal]
    (hA : Nat.card A = 3) : pCore 3 G ≤ centralizer (A : Set G) := by
  have hc := twoPerfect_centralizes_small_normal (pResidual 2 G) A
    (isPPerfect_pResidual 2) (Or.inr hA)
  apply le_trans ?_ hc
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have hcop : Nat.Coprime 2 (Nat.card (pCore 3 G)) := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  have ho : orderOf (⟨x, hx⟩ : pCore 3 G) = orderOf x :=
    (orderOf_injective (pCore 3 G).subtype (pCore 3 G).subtype_injective _).symm
  exact hcop.of_dvd_right (ho ▸ orderOf_dvd_natCard (⟨x, hx⟩ : pCore 3 G))

private theorem cubic_plane_eq_omega (E A B : Subgroup G)
    [IsElementaryAbelian 3 E] [A.Normal] [B.Normal]
    (hE : Nat.card E = 9) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hgen : E = A ⊔ B) (hr : primeRank 3 G ≤ 2) :
    E = (omega₁ (pCore 3 G) (p := 3)).map (pCore 3 G).subtype := by
  let : E.Normal := hgen.symm ▸ (inferInstance : (A ⊔ B).Normal)
  have hEP : E ≤ pCore 3 G := le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 3 E⟩
  have hEC : E ≤ centralizer (pCore 3 G : Set G) := by
    rw [hgen]
    exact sup_le (le_centralizer_iff.mp (core_centralizes_normal_cubic A hA))
      (le_centralizer_iff.mp (core_centralizes_normal_cubic B hB))
  apply le_antisymm
  · let : IsElementaryAbelian 3 (E.subgroupOf (pCore 3 G)) := IsElementaryAbelian.subgroupOf hEP
    have hm := map_mono (f := (pCore 3 G).subtype)
      (elementaryAbelian_le_omega₁ (p := 3) (E := E.subgroupOf (pCore 3 G)))
    rwa [map_subgroupOf_eq_of_le hEP] at hm
  · apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    intro x hx
    have hx3 : (x : G) ^ 3 = 1 := congrArg Subtype.val (by simpa using hx : x ^ 3 = 1)
    change (x : G) ∈ E
    by_contra hnot
    have hne : (x : G) ≠ 1 := by intro he; exact hnot (he ▸ E.one_mem)
    have ho : orderOf (x : G) = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3)).resolve_left
        (fun h => hne (orderOf_eq_one_iff.mp h))
    have hfix : E ≤ centralizer ({(x : G)} : Set G) := by
      intro e he
      exact mem_centralizer_singleton_iff.mpr (hEC he x x.property).symm
    have hl := IsElementaryAbelian.primeRank_ge_of_fixed_join E (x : G) ho hnot hfix
      (show Nat.card E = 3 ^ 2 from hE)
    omega

/-- Ω₁(O₃(J)), embedded in the same ambient quotient as J. -/
@[expose] def threeCoreOmega (J : Subgroup G) : Subgroup G :=
  ((omega₁ (pCore 3 J) (p := 3)).map (pCore 3 J).subtype).map J.subtype

omit [Finite G] in
/-- The iterated characteristic subgroup is normal whenever J is normal. -/
theorem threeCoreOmega_normal (J : Subgroup G) [J.Normal] : (threeCoreOmega J).Normal := by
  let : (omega₁ (pCore 3 J) (p := 3)).Characteristic := omega₁_characteristic _
  unfold threeCoreOmega
  infer_instance

omit [Finite G] in
private theorem image_normalized (M U V : Subgroup G)
    (hn : U ≤ normalizer (V : Set G)) :
    image M U ≤ normalizer (image M V : Set (CoreQuotient M)) := by
  have hh : U.subgroupOf M ≤ normalizer (V.subgroupOf M : Set M) := by
    intro u hu
    apply mem_normalizer_iff.mpr
    intro v
    exact mem_normalizer_iff.mp (hn hu) (v : G)
  exact (map_mono hh).trans ((V.subgroupOf M).le_normalizer_map (quotientMap M))

omit [Finite G] in
private theorem image_mono {M U V : Subgroup G} (hUV : U ≤ V) : image M U ≤ image M V :=
  map_mono (comap_mono hUV)

/-- The source omega calculation in the second literal quotient. The two
cubic factors need only be normal in the actual normal subgroup H. -/
theorem image_eq_omega_of_normal_cubics (M H Y X X₁ : Subgroup G)
    (hHM : H ≤ M) (hMH : M ≤ normalizer (H : Set G))
    (hXH : X ≤ H) (hX₁H : X₁ ≤ H)
    (hHX : H ≤ normalizer (X : Set G)) (hHX₁ : H ≤ normalizer (X₁ : Set G))
    (hgen : Y = X ⊔ X₁)
    [IsElementaryAbelian 3 (image M Y)]
    (hY : Nat.card (image M Y) = 9)
    (hX : Nat.card (image M X) = 3) (hX₁ : Nat.card (image M X₁) = 3)
    (hr : primeRank 3 M ≤ 2) :
    image M Y = threeCoreOmega (image M H) ∧ (image M Y).Normal := by
  let J := image M H
  have hHn : (H.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hHM).mpr hMH
  let := hHn
  have hJn : J.Normal := Subgroup.Normal.map hHn (quotientMap M) (QuotientGroup.mk'_surjective _)
  let := hJn
  have hYH : Y ≤ H := hgen ▸ sup_le hXH hX₁H
  have hEJ : image M Y ≤ J := image_mono hYH
  have hAJ : image M X ≤ J := image_mono hXH
  have hBJ : image M X₁ ≤ J := image_mono hX₁H
  let E := (image M Y).subgroupOf J
  let A := (image M X).subgroupOf J
  let B := (image M X₁).subgroupOf J
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.subgroupOf hEJ
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hAJ).mpr (image_normalized M H X hHX)
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer hBJ).mpr (image_normalized M H X₁ hHX₁)
  have hEA : E = A ⊔ B := by
    change (image M Y).subgroupOf J = _
    rw [← subgroupOf_sup hAJ hBJ]
    congr 1
    rw [hgen]
    unfold image
    rw [subgroupOf_sup (hXH.trans hHM) (hX₁H.trans hHM), Subgroup.map_sup]
  have he := cubic_plane_eq_omega E A B
    ((Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv).trans hY)
    ((Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hX)
    ((Nat.card_congr (subgroupOfEquivOfLe hBJ).toEquiv).trans hX₁) hEA
    ((Theory.GroupTheory.primeRank_le_of_injective 3 J.subtype J.subtype_injective).trans
      (three_rank_quotient_le M hr))
  have hm := congrArg (Subgroup.map J.subtype) he
  rw [map_subgroupOf_eq_of_le hEJ] at hm
  have hEq : image M Y = threeCoreOmega J := hm
  exact ⟨hEq, hEq.symm ▸ threeCoreOmega_normal J⟩

end CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.OmegaEndgame


public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.OmegaEndgame
open FamilySource LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G]

/-- The source normal closure is normalized by its defining overgroup. -/
theorem sourceClosure_normalized (M X : Subgroup G) :
    M ≤ normalizer (sourceClosure M X : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
  rw [← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

private theorem sup_perfect (X X₁ : Subgroup G) (hX : IsPPerfect 2 X)
    (hX₁ : IsPPerfect 2 X₁) : IsPPerfect 2 (X ⊔ X₁ : Subgroup G) := by
  let Y := X ⊔ X₁
  let R := (pResidual 2 Y).map Y.subtype
  have hle (A : Subgroup G) (hp : IsPPerfect 2 A) (hAY : A ≤ Y) : A ≤ R := by
    have he : (pResidual 2 A).map A.subtype = A := by
      rw [(pResidual_eq_top_iff 2 A).mpr hp, ← MonoidHom.range_eq_map, range_subtype]
    exact he ▸ embedded_pResidual_mono 2 hAY
  have hYR : Y ≤ R := sup_le (hle X hX le_sup_left) (hle X₁ hX₁ le_sup_right)
  apply (pResidual_eq_top_iff 2 Y).mp
  apply top_unique
  intro y _
  obtain ⟨r, hr, he⟩ := hYR y.property
  exact (Subtype.ext he : r = y) ▸ hr

variable [Finite G]

/-- The source normal closure has the claimed omega image in M₂/O₂(M₂),
and residual recovery proves its actual M₂-normality. The second image,
its cardinality, and quotient rank are all constructed internally. -/
theorem source_omega_and_second_normality
    (T : Sylow 2 G) (Z M₁ M₂ X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hCM₁ : centralizer (Z : Set G) ≤ M₁) (hCM₂ : centralizer (Z : Set G) ≤ M₂)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hnon : ¬ M₁ ≤ normalizer (X : Set G))
    [IsElementaryAbelian 3 (image M₁ (sourceClosure M₁ X))]
    (hY : Nat.card (image M₁ (sourceClosure M₁ X)) = 9)
    (hB : Nat.card (image M₁ X) = 3) (hr : primeRank 3 M₂ ≤ 2)
    (h10 : ∀ D ∈ NormalCentralizerXi (T : Subgroup G) Z, ∀ N : Subgroup G,
      IsMaximalTwoLocal N → D ⊔ (T : Subgroup G) ≤ N →
      D ≤ N ⊓ centralizer (localV (T : Subgroup G) N : Set G)) :
    image M₂ (sourceClosure M₁ X) =
      threeCoreOmega (image M₂ (M₂ ⊓ centralizer (localV (T : Subgroup G) M₂ : Set G))) ∧
      M₂ ≤ normalizer (sourceClosure M₁ X : Set G) := by
  obtain ⟨A, hAn, hA3, hAmem, _, hgen, hYH, hYnH⟩ :=
    source_complement_in_second_action_centralizer T Z M₁ M₂ X hZT hTC hZne hZ
      hCM₁ hCM₂ hM₁ hM₂ hX hnon hY hB h10
  let Y := sourceClosure M₁ X
  let X₁ := lift M₁ A
  let H₂ := M₂ ⊓ centralizer (localV (T : Subgroup G) M₂ : Set G)
  have hgen' : Y = X ⊔ X₁ := hgen
  have hTM₁ := hTC.trans hCM₁
  have hTM₂ := hTC.trans hCM₂
  have hXM₁ := hX.2.1.trans hCM₁
  have hXM₂ := hX.2.1.trans hCM₂
  have hX₁M₂ := hAmem.2.1.trans hCM₂
  have hYM₁ : Y ≤ M₁ := map_subtype_le _
  have hYM₂ : Y ≤ M₂ := hYH.trans inf_le_left
  have hM₁Y : M₁ ≤ normalizer (Y : Set G) := sourceClosure_normalized M₁ X
  have hM₂H : M₂ ≤ normalizer (H₂ : Set G) := actionCentralizer_normalizes (T : Subgroup G) M₂
  have hHY : H₂ ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYH).mp hYnH
  have hCY₁ : Y.pCoreIn 2 ≤ M₁.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (p := 2) (Y := Y) (L := M₁) hYM₁ hM₁Y
  have hCY₂ : Y.pCoreIn 2 ≤ M₂.pCoreIn 2 :=
    (pCoreIn_mono_of_normalizes (p := 2) (Y := Y) (L := H₂) hYH hHY).trans
      (pCoreIn_mono_of_normalizes (p := 2) (Y := H₂) (L := M₂) inf_le_left hM₂H)
  obtain ⟨eY₁, _⟩ := coreQuotientEquivImage M₁ Y hYM₁ hCY₁
  obtain ⟨eY₂, _⟩ := coreQuotientEquivImage M₂ Y hYM₂ hCY₂
  let eY := eY₁.symm.trans eY₂
  let : IsElementaryAbelian 3 (image M₂ Y) := IsElementaryAbelian.of_surjective eY.toMonoidHom eY.surjective
  have hY₂ : Nat.card (image M₂ Y) = 9 := (Nat.card_congr eY.symm.toEquiv).trans hY
  have hc (D : Subgroup G) (hD : D ∈ NormalCentralizerXi (T : Subgroup G) Z)
      (M : Subgroup G) (hM : IsMaximalTwoLocal M) (hCM : centralizer (Z : Set G) ≤ M) :
      D ≤ M ⊓ centralizer (localV (T : Subgroup G) M : Set G) :=
    h10 D hD M hM (sup_le (hD.2.1.trans hCM) (hTC.trans hCM))
  have hCX₁ := core_le_of_action_control T Z M₁ X hZT hTM₁ hZ hX (hc X hX M₁ hM₁ hCM₁)
  have hCX₂ := core_le_of_action_control T Z M₂ X hZT hTM₂ hZ hX (hc X hX M₂ hM₂ hCM₂)
  obtain ⟨eX₁, _⟩ := coreQuotientEquivImage M₁ X hXM₁ hCX₁
  obtain ⟨eX₂, _⟩ := coreQuotientEquivImage M₂ X hXM₂ hCX₂
  have hBX₂ : Nat.card (image M₂ X) = 3 :=
    (Nat.card_congr (eX₂.symm.trans eX₁).toEquiv).trans hB
  have hCX₁₂ := core_le_of_action_control T Z M₂ X₁ hZT hTM₂ hZ hAmem
    (hc X₁ hAmem M₂ hM₂ hCM₂)
  obtain ⟨eX₁₂, _⟩ := coreQuotientEquivImage M₂ X₁ hX₁M₂ hCX₁₂
  obtain ⟨eA, _⟩ := prime_lift_quotient M₁ A hA3
  have hBX₁₂ : Nat.card (image M₂ X₁) = 3 :=
    (Nat.card_congr (eX₁₂.symm.trans eA).toEquiv).trans hA3
  have hHC : H₂ ≤ centralizer (Z : Set G) :=
    inf_le_right.trans (action_centralizer_le T Z M₂ hZT hTM₂ hZ)
  obtain ⟨hOmega, hNormal⟩ := image_eq_omega_of_normal_cubics M₂ H₂ Y X X₁
    inf_le_left hM₂H (hc X hX M₂ hM₂ hCM₂) (hc X₁ hAmem M₂ hM₂ hCM₂)
    (hHC.trans hX.2.2) (hHC.trans hAmem.2.2) hgen hY₂ hBX₂ hBX₁₂ hr
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := by
    rw [hgen']
    exact (le_inf hX.1.1 hAmem.1.1).trans (normalizer_inf_normalizer_le_normalizer_sup X X₁)
  have hpY : IsPPerfect 2 Y := hgen'.symm ▸ sup_perfect X X₁ hX.1.2.1 hAmem.1.2.1
  have hpY₂ : IsPPerfect 2 (Y.subgroupOf M₂) := hpY.of_surjective
    (subgroupOfEquivOfLe hYM₂).symm.toMonoidHom (subgroupOfEquivOfLe hYM₂).symm.surjective
  have hk : IsPGroup 2 (quotientMap M₂).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : ((Y.subgroupOf M₂).map (quotientMap M₂)).Normal := hNormal
  have hYn : (Y.subgroupOf M₂).Normal := normal_of_map_normal_of_pPerfect
    (quotientMap M₂) (Y.subgroupOf M₂) hpY₂ hk (core_normalizes T hTM₂ hTY)
  exact ⟨hOmega, (normal_subgroupOf_iff_le_normalizer hYM₂).mp hYn⟩

/-- The final normal-closure contradiction of 15.4.8. The source rank/core
outputs in the first quotient and universal 15.4.10 remain with the existing
centralizer owners. No second-quotient model, Y-normality or generation of G
by M₁ and M₂ is an input. -/
theorem source_contradiction
    (T : Sylow 2 G) (Z M₁ M₂ X : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZ : Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hCM₁ : centralizer (Z : Set G) ≤ M₁) (hCM₂ : centralizer (Z : Set G) ≤ M₂)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂) (hneM : M₁ ≠ M₂)
    (hEC : HasCharacteristicTwo M₁)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hnon : ¬ M₁ ≤ normalizer (X : Set G))
    [IsElementaryAbelian 3 (image M₁ (sourceClosure M₁ X))]
    (hY : Nat.card (image M₁ (sourceClosure M₁ X)) = 9)
    (hB : Nat.card (image M₁ X) = 3) (hr : primeRank 3 M₂ ≤ 2)
    (h10 : ∀ D ∈ NormalCentralizerXi (T : Subgroup G) Z, ∀ N : Subgroup G,
      IsMaximalTwoLocal N → D ⊔ (T : Subgroup G) ≤ N →
      D ≤ N ⊓ centralizer (localV (T : Subgroup G) N : Set G)) : False := by
  have hM₂Y := (source_omega_and_second_normality T Z M₁ M₂ X hZT hTC hZne hZ
    hCM₁ hCM₂ hM₁ hM₂ hX hnon hY hB hr h10).2
  let Y := sourceClosure M₁ X
  have hYM₁ : Y ≤ M₁ := map_subtype_le _
  have hM₁Y : M₁ ≤ normalizer (Y : Set G) := sourceClosure_normalized M₁ X
  have hYne : Y ≠ ⊥ := by
    intro he
    have hi : image M₁ Y = ⊥ := by rw [he, image, bot_subgroupOf, Subgroup.map_bot]
    have hh := hY
    change Nat.card (image M₁ Y) = 9 at hh
    rw [hi, Nat.card_unique] at hh
    omega
  have hcore : Y.pCoreIn 2 ≠ ⊥ := coreIn_ne_bot_of_normal hEC hYne hYM₁
    ((normal_subgroupOf_iff_le_normalizer hYM₁).mpr hM₁Y)
  have hn := normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  have hL : IsTwoLocal (normalizer (Y.pCoreIn 2 : Set G)) :=
    ⟨Y.pCoreIn 2, hcore, isPGroup_pCoreIn 2 Y, rfl⟩
  have hM₂M₁ : M₂ ≤ M₁ := (hM₂Y.trans hn).trans (hM₁.2 hL (hM₁Y.trans hn))
  exact hneM (hM₂.eq_of_le hM₁.1 hM₂M₁).symm

end CFSG.Quasithin.Chapter15.Section04.CentralizerNormalClosureCubic.OmegaEndgame
