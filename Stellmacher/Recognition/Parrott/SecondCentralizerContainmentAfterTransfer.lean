module

public import Theory.GroupTheory.SolvableCentralElementaryFusion
public import Stellmacher.Recognition.Parrott.SecondCentralizerOddObstruction
public import Stellmacher.Recognition.Parrott.SecondCentralizerFirstTransfer
public import Stellmacher.Recognition.Parrott.NormalizerElementaryFusion
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Containment of the second centralizer after transfer

Write N=N_G(F), K=O₂(N), W=Ω₁(K), and C=C_G(v). The two transfer
steps supply M of index two in C, L normal of index two in M, and a
Sylow two-subgroup of L with ambient image Y. We prove C≤N from the
specified identities Ω₁(Y)=F and Z(Y)=Z(W).

The N₂ hypothesis makes C, hence L, solvable. Put ZK=Z(K). Since
ZK≤Z(Y), the solvable central elementary supplement puts its L-conjugates
inside Y. These involutions lie in F. The checked fusion in F separates
the three nonidentity points of ZK from all other involutions in F, so ZK
is normal in L. The odd-subgroup obstruction makes C_L(ZK) a two-group;
it is therefore the normal Sylow subgroup Y. This step is packaged in
`Sylow.normal_of_central_elementary_fusion`.

A normal Sylow is characteristic, so normality of L in M makes M normalize
Y and Ω₁(Y)=F. Finally the local Sylow subgroup P of C lies in N and
has twice the order of M∩P=W. Thus C=M P≤N.

The shorter theorem records the premises actually used. The final wrapper
accepts the entire agreed second-transfer interface, including the cyclic
order-four witness and the cardinality identities, without adding premises.
No ambient centralizer-containment theorem is imported.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, printed p.683 (PDF p.12). Solvability replaces the quotient-centralizer
and transfer argument in that paragraph.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The center and omega identities of the actual second-transfer Sylow suffice
for ambient containment. The additional order-four data are not needed here. -/
public theorem second_centralizer_le_normalizer_of_omega_sylow
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X0 := K.map N.subtype
    let D := (commutator X0).map X0.subtype
    let A := (Q : Subgroup N).map N.subtype
    X0 ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let ZW := (center (omega₁ K (p := 2))).map
      ((N.subtype.comp K.subtype).comp (omega₁ K (p := 2)).subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ (M : Subgroup C) (L : Subgroup M),
    M.index = 2 → M.map C.subtype ⊓ P = W → L.Normal →
    let LG := L.map (C.subtype.comp M.subtype)
    let Y := W ⊓ LG
    (omega₁ Y (p := 2)).map Y.subtype = d.F →
    (center Y).map Y.subtype = ZW →
    ∀ S : Sylow 2 L,
    (S : Subgroup L).map (C.subtype.comp (M.subtype.comp L.subtype)) = Y →
    C ≤ N := by
  intro N K X0 D A hCD v hv hfix W ZW C P M L hMi hMP hLn LG Y hYO hYZ S hS
  let : L.Normal := hLn
  let : Group.IsSolvable C := hN C (Theory.GroupTheory.isTwoLocal_involution_centralizer hv)
  let f : L →* G := C.subtype.comp (M.subtype.comp L.subtype)
  have hf : Function.Injective f :=
    C.subtype_injective.comp (M.subtype_injective.comp L.subtype_injective)
  let ZK := (center K).map (N.subtype.comp K.subtype)
  let E := ZK.comap f
  have hZKY : ZK ≤ (center Y).map Y.subtype := by
    rw [hYZ]
    exact d.normalizer_core_omega_inclusions.2.1
  have hZY : ZK ≤ Y := hZKY.trans (map_subtype_le _)
  have hZrange : ZK ≤ f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype, map_map]
    exact hZY.trans inf_le_right
  have hEmap : E.map f = ZK := map_comap_eq_self hZrange
  have hES : E ≤ S := by
    intro x hx
    obtain ⟨s, hs, he⟩ := hS.symm ▸ hZY hx
    exact hf he ▸ hs
  have hEc : E ≤ centralizer (S : Set L) := by
    intro x hx y hy
    apply hf
    obtain ⟨a, ha, he⟩ := hZKY hx
    have hyY : f y ∈ Y := hS ▸ mem_map_of_mem f hy
    have hh := congrArg Y.subtype (mem_center_iff.mp ha ⟨f y, hyY⟩)
    change f y * (a : G) = (a : G) * f y at hh
    change (a : G) = f x at he
    rw [he] at hh
    simpa only [map_mul] using hh
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hEF (x : L) (hx : x ∈ E) : f x ∈ d.F := d.normalizer_core_center_le hx
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro x y
      apply Subtype.ext
      apply hf
      change f (x : L) * f (y : L) = f (y : L) * f (x : L)
      exact setLike_mul_comm (hEF x x.property) (hEF y y.property))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      apply hf
      change f ((x : L) ^ 2) = f 1
      simpa only [map_pow, map_one] using
        elemPow_eq_one_of_isElementaryAbelian (f x) (hEF x x.property)) }
  have hfusion : ∀ g x : L, x ∈ E → g * x * g⁻¹ ∈ (S : Subgroup L) →
      g * x * g⁻¹ ∈ E := by
    intro g x hx hret
    by_cases hx1 : x = 1
    · simp [hx1]
    have hfx1 : f x ≠ 1 := fun hh => hx1 (hf (hh.trans f.map_one.symm))
    have hfx2 : orderOf (f x) = 2 :=
      (Nat.prime_two.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one
        (elemPow_eq_one_of_isElementaryAbelian (f x) (hEF x hx)))).resolve_left
          (fun he => hfx1 (orderOf_eq_one_iff.mp he))
    have hretY : f (g * x * g⁻¹) ∈ Y := hS ▸ mem_map_of_mem f hret
    have hretF : f (g * x * g⁻¹) ∈ d.F := by
      rw [← hYO]
      refine ⟨⟨f (g * x * g⁻¹), hretY⟩, subset_closure ?_, rfl⟩
      apply Subtype.ext
      change (f (g * x * g⁻¹)) ^ (2 ^ 1) = 1
      simp only [map_mul, map_inv, pow_one]
      change ((MulAut.conj (f g)) (f x)) ^ 2 = 1
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (f x) (hEF x hx), map_one]
    by_contra hout
    obtain ⟨a, ha⟩ := (d.normalizer_elementary_fusion_in_join h hN hproper Q hCD v hv hfix).1
      (f x) hx hfx2
    obtain ⟨b, hb⟩ := (d.normalizer_elementary_fusion_in_join h hN hproper Q hCD v hv hfix).2
      (f (g * x * g⁻¹)) hretF hout
    have hzx : IsConj z (f x) := isConj_iff.mpr ⟨a, ha⟩
    have hxr : IsConj (f x) (f (g * x * g⁻¹)) :=
      isConj_iff.mpr ⟨f g, by simp only [map_mul, map_inv]⟩
    have hvr : IsConj v (f (g * x * g⁻¹)) := isConj_iff.mpr ⟨b, hb⟩
    exact (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).2.2.2.1
      ((hzx.trans hxr).trans hvr.symm)
  have hodd : ∀ O : Subgroup L, Odd (Nat.card O) → E ≤ normalizer (O : Set L) →
      O = ⊥ := by
    intro O ho hEO
    have hOG : O.map f = ⊥ := d.second_centralizer_odd_subgroup_eq_bot
      h hN hproper Q v hv hfix (O.map f)
      (by rintro _ ⟨x, _, rfl⟩; exact x.val.val.property)
      (by rwa [card_map_of_injective hf])
      (by
        change ZK ≤ normalizer (O.map f : Set G)
        rw [← hEmap]
        exact (map_mono hEO).trans (O.le_normalizer_map f))
    exact map_injective hf (hOG.trans (map_bot f).symm)
  have hSn : (S : Subgroup L).Normal :=
    S.normal_of_central_elementary_fusion inferInstance E hES hEc hfusion hodd
  let : (S : Subgroup L).Characteristic := S.characteristic_of_normal hSn
  let B := (S : Subgroup L).map L.subtype
  have hMY : M.map C.subtype ≤ normalizer (Y : Set G) := by
    have hBn : B.Normal := inferInstance
    have hh := B.le_normalizer_map (C.subtype.comp M.subtype)
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, MonoidHom.range_comp,
      range_subtype] at hh
    simpa only [B, map_map, MonoidHom.comp_assoc, hS] using hh
  let : (omega₁ Y (p := 2)).Characteristic := omega₁_characteristic _
  have hMN : M.map C.subtype ≤ N := by
    have hh := hMY.trans (normalizer_le_normalizer_characteristic_image Y
      (omega₁ Y (p := 2)))
    rwa [hYO] at hh
  have hPN : P ≤ N := inf_le_left.trans d.sylow_le_normalizer
  have hex : ∃ w : G, w ∈ P ∧ w ∉ M.map C.subtype := by
    by_contra! hn
    have hPW : P = W := by rw [← hMP, inf_eq_right.mpr hn]
    have hcP : Nat.card P = 512 := d.normalizer_fixed_sylow_card h hN hproper Q v hv hfix
    have hcW : Nat.card W = 256 :=
      (card_map_of_injective (f := N.subtype.comp K.subtype)
        (K := omega₁ K (p := 2)) (N.subtype_injective.comp K.subtype_injective)).trans
        (d.normalizer_core_omega_structure h hN hproper).1
    rw [hPW, hcW] at hcP
    omega
  obtain ⟨w, hwP, hwM⟩ := hex
  intro x hxC
  let wC : C := ⟨w, hwP.2⟩
  let xC : C := ⟨x, hxC⟩
  have hw : wC ∉ M := fun hh => hwM (mem_map_of_mem C.subtype hh)
  by_cases hx : xC ∈ M
  · exact hMN (mem_map_of_mem C.subtype hx)
  · have hprod : wC * xC ∈ M := (mul_mem_iff_of_index_two hMi).mpr (iff_of_false hw hx)
    have hprodN : w * x ∈ N := hMN (mem_map_of_mem C.subtype hprod)
    exact (N.mul_mem_cancel_left (hPN hwP)).mp hprodN

/-- Containment from the complete agreed second-transfer construction interface.
All intermediate premises are supplied explicitly; no source from the construction
of the second transfer is required. -/
public theorem second_centralizer_le_normalizer_of_second_transfer
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let X0 := K.map N.subtype
    let D := (commutator X0).map X0.subtype
    let A := (Q : Subgroup N).map N.subtype
    X0 ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let ZW := (center (omega₁ K (p := 2))).map
      ((N.subtype.comp K.subtype).comp (omega₁ K (p := 2)).subtype)
    let C := centralizer ({v} : Set G)
    let P := (d.sylow : Subgroup G) ⊓ C
    ∀ (M : Subgroup C) (L : Subgroup M),
    M.Normal → M.index = 2 → M.map C.subtype ⊓ P = W →
    L.Normal → L.index = 2 →
    let LG := L.map (C.subtype.comp M.subtype)
    let Y := W ⊓ LG
    ∀ b : G, b ∈ X0 → orderOf b = 4 → b ^ 2 = v →
    X0 ⊓ centralizer (A : Set G) = zpowers b → b ∉ LG →
    Nat.card Y = 128 → (omega₁ Y (p := 2)).map Y.subtype = d.F →
    (center Y).map Y.subtype = ZW →
    ∀ S : Sylow 2 L,
    (S : Subgroup L).map (C.subtype.comp (M.subtype.comp L.subtype)) = Y →
    C ≤ N := by
  intro N K X0 D A hCD v hv hfix W ZW C P M L _hMn hMi hMP hLn _hLi
    LG Y b _hb _hb4 _hb2 _hbC _hbL _hYcard hYO hYZ S hS
  exact d.second_centralizer_le_normalizer_of_omega_sylow h hN hproper Q
    hCD v hv hfix M L hMi hMP hLn hYO hYZ S hS

end Stellmacher.Recognition.ParrottSecondElementaryData
