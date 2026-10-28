module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.QuotientRecognition.Model
public import GorensteinWalter.FinalTheorem
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.PSL2InvolutionFusion
public import GorensteinWalter.PSL2Cardinality
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# Recognition of Held's central root quotient as A7

An odd-core-free finite group with a dihedral Sylow subgroup of order eight,
an embedded A6, and the actual A7 involution centralizer is A7. No simplicity
hypothesis is required.

Gorenstein–Walter gives a two-group, A7, or an odd-index normal PSL2/PGL2
subgroup. The embedded A6 excludes the two-group case and lies in every
normal odd-index subgroup. It also excludes the PGL2 branch: its normal
PSL2 subgroup of index two would force sixteen to divide the ambient order.
The A7 centralizer has no nontrivial odd image, so it lies in the normal
PSL2 subgroup. Fusion of PSL2 involutions then forces this subgroup to be
the whole group. Its centralizer of order 24 forces field order 23 or 25;
neither group order is divisible by the order 360 of the embedded A6.

The final application uses the literal `rootQuotient` and `quotientSixEquiv`.
Its odd-core, Sylow and centralizer hypotheses remain the separate local
geometry obligations of the root-factor assembly.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, printed p.237.
-/

open Subgroup GorensteinWalter

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor
universe u v

namespace QuotientRecognition
variable {H : Type u} [Group H]

private theorem six_card {A : Subgroup H} (e : A ≃* alternatingGroup (Fin 6)) : Nat.card A = 360 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem six_le_normal {A N : Subgroup H} (e : A ≃* alternatingGroup (Fin 6))
    [N.Normal] (hN : ¬ 360 ∣ N.index) : A ≤ N := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup A := e.isSimpleGroup
  let f : A →* H ⧸ N := (QuotientGroup.mk' N).comp A.subtype
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · have hd := Subgroup.card_dvd_of_injective f (f.ker_eq_bot_iff.mp hbot)
    rw [six_card e, ← N.index_eq_card] at hd
    exact (hN hd).elim
  · intro a ha
    have hk : (⟨a, ha⟩ : A) ∈ f.ker := htop ▸ mem_top _
    exact (QuotientGroup.eq_one_iff a).mp hk

private theorem six_le_normal_odd {A N : Subgroup H} (e : A ≃* alternatingGroup (Fin 6))
    [N.Normal] (hN : Odd N.index) : A ≤ N := by
  apply six_le_normal e
  intro h
  exact hN.not_two_dvd_nat ((by decide : 2 ∣ 360).trans h)

private theorem not_sixteen_dvd [Finite H] (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4) : ¬ 16 ∣ Nat.card H := by
  intro h
  have hd := S.pow_dvd_card_of_pow_dvd_card (n := 4) h
  have hc : Nat.card S = 8 := (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  rw [hc] at hd
  norm_num at hd

private theorem no_index_two (h16 : ¬ 16 ∣ Nat.card H)
    {A : Subgroup H} (e : A ≃* alternatingGroup (Fin 6))
    (N : Subgroup H) [N.Normal] : N.index ≠ 2 := by
  intro hN
  have hAN : A ≤ N := six_le_normal e (by rw [hN]; decide)
  have hd : 8 ∣ Nat.card N := (by decide : 8 ∣ 360).trans
    (six_card e ▸ card_dvd_of_le hAN)
  have hmul : Nat.card N * 2 = Nat.card H := by simpa [hN] using N.card_mul_index
  apply h16
  rw [← hmul]
  exact Nat.mul_dvd_mul hd (dvd_refl 2)

private theorem six_in_normal {A N : Subgroup H} (e : A ≃* alternatingGroup (Fin 6))
    [N.Normal] (hN : Odd N.index) :
    Nonempty (A.subgroupOf N ≃* alternatingGroup (Fin 6)) :=
  ⟨(subgroupOfEquivOfLe (six_le_normal_odd e hN)).trans e⟩

private theorem not_pgroup [Finite H] {A : Subgroup H} (e : A ≃* alternatingGroup (Fin 6)) :
    ¬ IsPGroup 2 H := by
  intro h
  have hA := h.to_subgroup A
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdiv : 3 ∣ 2 ^ n := by
    rw [← hn, six_card e]
    decide
  exact (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv)

private theorem not_pgl {F : Type v} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (h16 : ¬ 16 ∣ Nat.card H)
    {A : Subgroup H} (eA : A ≃* alternatingGroup (Fin 6))
    (e : H ≃* PGL2 F) : False := by
  let R : Subgroup (PGL2 F) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  have hR : R.index = 2 := pgl2_psl2Range_index_eq_two F hF
  let : R.Normal := R.normal_of_index_eq_two hR
  let N := R.comap e.toMonoidHom
  have hN : N.index = 2 := (R.index_comap_of_surjective e.surjective).trans hR
  exact no_index_two h16 eA N hN

private theorem normal_eq_top_of_fusion (N : Subgroup H) [N.Normal]
    (t : H) (ht : orderOf t = 2) (hCN : centralizer ({t} : Set H) ≤ N)
    (hfusion : ∀ x y : N, IsInvolution x → IsInvolution y →
      ∃ g : N, g * x * g⁻¹ = y) : N = ⊤ := by
  have htN : t ∈ N := hCN (mem_centralizer_singleton_iff.mpr rfl)
  let tN : N := ⟨t, htN⟩
  have htI : IsInvolution tN := by
    constructor
    · intro h
      have he : t = 1 := congrArg Subtype.val h
      simp [he] at ht
    · apply Subtype.ext
      exact ht ▸ pow_orderOf_eq_one t
  apply top_le_iff.mp
  intro g _
  let t' : N := MulAut.conjNormal (H := N) g tN
  have ht'I : IsInvolution t' := by
    constructor
    · intro h
      exact htI.1 ((MulAut.conjNormal g).injective (h.trans (map_one _).symm))
    · simpa only [map_pow, map_one] using congrArg (MulAut.conjNormal (H := N) g) htI.2
  obtain ⟨n, hn⟩ := hfusion t' tN ht'I htI
  have hng : (n : H) * g ∈ centralizer ({t} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    have he : (n : H) * (g * t * g⁻¹) * (n : H)⁻¹ = t := congrArg Subtype.val hn
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (n * g) * t * (n * g)⁻¹ = (n : H) * (g * t * g⁻¹) * (n : H)⁻¹ := by group
      _ = t := he
  simpa using N.mul_mem (N.inv_mem n.property) (hCN hng)

private theorem normal_psl_eq_top {F : Type v} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F))
    (N : Subgroup H) [N.Normal] (e : N ≃* PSL2 F)
    (t : H) (ht : orderOf t = 2) (hCN : centralizer ({t} : Set H) ≤ N) : N = ⊤ := by
  apply normal_eq_top_of_fusion N t ht hCN
  intro x y hx hy
  have hmap (a : N) (ha : IsInvolution a) : IsInvolution (e a) := by
    refine ⟨fun h => ha.1 (e.injective (h.trans (map_one e).symm)), ?_⟩
    simpa only [map_pow, map_one] using congrArg e ha.2
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power
    F hF (e x) (e y) (hmap x hx) (hmap y hy)
  refine ⟨e.symm g, ?_⟩
  apply e.injective
  simpa only [map_mul, map_inv, e.apply_symm_apply] using hg

private theorem not_psl_of_centralizer_twentyfour
    {F : Type v} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : H ≃* PSL2 F)
    (t : H) (ht : orderOf t = 2)
    (hC : Nat.card (centralizer ({t} : Set H)) = 24)
    {A : Subgroup H} (eA : A ≃* alternatingGroup (Fin 6)) : False := by
  have htI : IsInvolution (e t) := by
    refine ⟨?_, ?_⟩
    · intro h
      have he : t = 1 := e.injective (h.trans (map_one e).symm)
      simp [he] at ht
    · have h : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
      simpa only [map_pow, map_one] using congrArg e h
  have hc : Nat.card (centralizer ({e t} : Set (PSL2 F))) = 24 := by
    let ec : centralizer ({t} : Set H) ≃* centralizer ({e t} : Set (PSL2 F)) := {
      toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
        simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
      invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
        apply e.injective
        simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property)⟩
      left_inv x := Subtype.ext (e.symm_apply_apply x)
      right_inv y := Subtype.ext (e.apply_symm_apply y)
      map_mul' x y := Subtype.ext (e.map_mul x y) }
    exact (Nat.card_congr ec.toEquiv).symm.trans hC
  obtain ⟨T, s, _, _, hsI, hsT, hinv, hcent, _, hcard⟩ :=
    psl2_reflected_torus_card hF htI
  have hsN : s ∈ normalizer T := by
    rw [mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      change s * y * s⁻¹ ∈ T
      rw [hinv y hy]
      exact T.inv_mem hy
    · intro x hx
      refine ⟨x⁻¹, T.inv_mem hx, ?_⟩
      change s * x⁻¹ * s⁻¹ = x
      rw [hinv x⁻¹ (T.inv_mem hx), inv_inv]
  have hdouble := card_sup_zpowers_of_normalizing_involution T s hsI.2 hsT hsN
  rw [← hcent, hc] at hdouble
  have htwelve : Nat.card T = 12 := by omega
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _, hp, _, he⟩ := hF
    rw [he]
    exact hp.pow
  have hq : Nat.card F = 23 ∨ Nat.card F = 25 := by
    obtain ⟨k, hk⟩ := hodd
    rcases hcard with hm | hp <;> omega
  have hd : 360 ∣ Nat.card (PSL2 F) := by
    rw [← Nat.card_congr e.toEquiv, ← six_card eA]
    exact A.card_subgroup_dvd_card
  rw [psl2_card_formula F hF] at hd
  rcases hq with hq | hq <;> norm_num [hq] at hd

/-- Held's recognition step: an odd-core-free group with Sylow group D8,
an embedded A6, and the actual A7 involution centralizer is A7. -/
public theorem recognize {H : Type u} [Group H] [Finite H]
    (hO : pPrimeCore 2 H = ⊥)
    (hSylow : ∃ S : Sylow 2 H, Nonempty (S ≃* DihedralGroup 4))
    (hSix : ∃ A : Subgroup H, Nonempty (A ≃* alternatingGroup (Fin 6)))
    (hC : ∃ t : H, orderOf t = 2 ∧
      Nonempty (centralizer ({t} : Set H) ≃* sevenInvolutionCentralizer)) :
    Nonempty (H ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨S, ⟨eS⟩⟩ := hSylow
  obtain ⟨A, ⟨eA⟩⟩ := hSix
  obtain ⟨t, ht, ⟨eC⟩⟩ := hC
  have hdihedral : HasDihedralSylowTwo H := by
    intro T
    exact ⟨2, by decide, ⟨(Sylow.equiv T S).trans eS⟩⟩
  let eQ : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientBot (G := H))
  rcases gorensteinWalter H hdihedral with ⟨_, htwo⟩ | ⟨_, ⟨eSeven⟩⟩ |
      ⟨_, F, hF, L, hLN, hLi, hLm⟩
  · exact (not_pgroup eA (htwo.of_equiv eQ)).elim
  · exact ⟨eQ.symm.trans eSeven⟩
  · let N := L.map eQ.toMonoidHom
    let eN : L ≃* N := Subgroup.equivMapOfInjective L eQ.toMonoidHom eQ.injective
    let : N.Normal := hLN.map eQ.toMonoidHom eQ.surjective
    have hNi : Odd N.index := by
      rw [show N.index = L.index from L.index_map_equiv eQ]
      exact hLi
    obtain ⟨eAN⟩ := six_in_normal (N := N) eA hNi
    rcases hLm with ePSL | ePGL
    · have hCN : centralizer ({t} : Set H) ≤ N := by
        intro c hc
        let f : sevenInvolutionCentralizer →* H ⧸ N :=
          (QuotientGroup.mk' N).comp ((centralizer ({t} : Set H)).subtype.comp
            eC.symm.toMonoidHom)
        have he := Model.hom_to_odd_trivial (K := H ⧸ N)
          (by simpa only [← N.index_eq_card] using hNi) f (eC ⟨c, hc⟩)
        apply (QuotientGroup.eq_one_iff c).mp
        simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          eC.symm_apply_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply] using he
      have hNtop := normal_psl_eq_top hF N (eN.symm.trans ePSL.some) t ht hCN
      let eH : H ≃* PSL2 F :=
        ((MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv).symm.trans
          (eN.symm.trans ePSL.some)
      have hc : Nat.card (centralizer ({t} : Set H)) = 24 :=
        (Nat.card_congr eC.toEquiv).trans Model.centralizer_card
      exact (not_psl_of_centralizer_twentyfour hF eH t ht hc eA).elim
    · have hN16 : ¬ 16 ∣ Nat.card N := fun h =>
        not_sixteen_dvd S eS (h.trans N.card_subgroup_dvd_card)
      exact (not_pgl hF hN16 eAN (eN.symm.trans ePGL.some)).elim

end QuotientRecognition

/-- Application to the literal central root quotient. The embedded A6 is
supplied by `quotientSixEquiv`, not an additional recognition premise. -/
public theorem rootQuotient_equiv_seven_of_local_geometry
    {G : Type u} [Group G] [Finite G] (D : HeldM22A10.LocalData G)
    (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
    (L : Source.SixLocalData D e)
    (hO : pPrimeCore 2 (rootQuotient D e L) = ⊥)
    (hSylow : ∃ S : Sylow 2 (rootQuotient D e L), Nonempty (S ≃* DihedralGroup 4))
    (hC : ∃ t : rootQuotient D e L, orderOf t = 2 ∧
      Nonempty (centralizer ({t} : Set (rootQuotient D e L)) ≃*
        sevenInvolutionCentralizer)) :
    Nonempty (rootQuotient D e L ≃* alternatingGroup (Fin 7)) :=
  QuotientRecognition.recognize hO hSylow
    ⟨quotientSix D e L, ⟨quotientSixEquiv D e L⟩⟩ hC

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor
