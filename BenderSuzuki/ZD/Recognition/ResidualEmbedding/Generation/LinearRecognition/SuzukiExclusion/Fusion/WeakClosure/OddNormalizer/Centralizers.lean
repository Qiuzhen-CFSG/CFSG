module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.TorusNormalization

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.CommonPrime
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Bounds
public import Theory.GroupAction.CoprimeCentralizerLift

/-!
# The Suzuki quotient normalizer centralizers

Coprime fixed-point lifting through the elementary subgroup M° puts the
centralizer of every nonidentity torus element into the image of D.
Intersecting with the image of N_M(S) gives (14G); intersecting with S-bar
identifies its fixed subgroup with U-bar. The torus normalizes both T and S,
and the full normalizer of S-bar is the image of N_M(S).

These are deductions on the literal quotient M/(M°.subgroupOf M).
They do not yet prove invariance of U-bar under its full normalizer.
Source: GLS4, Chapter 2, Lemma 14.9 and equation (14G),
`refs/KGroup/GLS4/Chapter2.tex`, lines 2600–2620.
-/

noncomputable section

open Subgroup Theory.GroupTheory
open scoped Pointwise
open scoped IsMulCommutative

private theorem centralizer_quotient_eq {H : Type*} [Group H] [Finite H]
    (A : Subgroup H) [A.Normal] [IsMulCommutative A] (x : H)
    (hcop : Nat.Coprime (orderOf x) (Nat.card A)) :
    centralizer ({QuotientGroup.mk' A x} : Set (H ⧸ A)) =
      (centralizer ({x} : Set H)).map (QuotientGroup.mk' A) := by
  let pi := QuotientGroup.mk' A
  apply le_antisymm ?_
    (by simpa only [Set.image_singleton] using
      map_centralizer_le_centralizer_image ({x} : Set H) pi)
  intro y hy
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective A y
  have hcomm : Commute (pi x) (pi v) :=
    (mem_centralizer_singleton_iff.mp hy).symm
  have hv := mem_centralizer_sup_of_coprime_fixed_coset (⊤ : Subgroup H) A
    (zpowers x) le_top (by rw [(⊤ : Subgroup H).normalizer_eq_top]; exact le_top) (by rw [A.normalizer_eq_top]; exact le_top)
    (by simpa only [Nat.card_zpowers] using hcop) v (mem_top _) (by
      intro a ha
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      apply (QuotientGroup.eq_one_iff _).mp
      change pi ((x ^ i) * v * (x ^ i)⁻¹ / v) = 1
      simp only [map_div, map_mul, map_inv, map_zpow]
      rw [(hcomm.zpow_left i).eq, mul_inv_cancel_right, div_self'])
  have him := mem_map_of_mem pi hv
  simpa only [Subgroup.map_sup, top_inf_eq, zpowers_eq_closure, centralizer_closure,
    (Subgroup.map_eq_bot_iff A).mpr (show A ≤ pi.ker by rw [QuotientGroup.ker_mk']), sup_bot_eq] using him

private theorem map_inf_of_ker_le {H Q : Type*} [Group H] [Group Q]
    (f : H →* Q) (R D : Subgroup H) (hk : f.ker ≤ R) :
    (R ⊓ D).map f = R.map f ⊓ D.map f := by
  apply le_antisymm (map_inf_le _ _ _) ?_
  rintro y ⟨⟨r, hr, hrf⟩, ⟨v, hv, hvf⟩⟩
  have hrv : r⁻¹ * v ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrf, hvf, inv_mul_cancel]
  have hvR : v ∈ R := by
    simpa only [mul_inv_cancel_left] using R.mul_mem hr (hk hrv)
  exact ⟨v, ⟨hvR, hv⟩, hvf⟩

private theorem map_normalizer_of_ker_le {H Q : Type*} [Group H] [Group Q]
    (f : H →* Q) (hf : Function.Surjective f) (R : Subgroup H)
    (hk : f.ker ≤ R) : (normalizer (R : Set H)).map f = normalizer (R.map f : Set Q) := by
  apply (comap_injective hf)
  rw [comap_map_eq_self (hk.trans R.le_normalizer),
    comap_normalizer_eq_of_surjective _ hf, comap_map_eq_self hk]

namespace BenderSuzuki.ZD.SuzukiExclusion
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem Context.quotient_torus_centralizer_le_pair (d : Context Z M z t m)
    (hsemi : TorusSemiregular M t) {x : G}
    (hx : x ∈ residualCommutator M t) (hx1 : x ≠ 1) :
    let A := closure (Z ∩ (M : Set G))
    letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' (A.subgroupOf M)
    let xM : M := ⟨x, (show residualCommutator M t ≤ M by rw [d.torus_eq_local_pair]; exact inf_le_left.trans inf_le_left) hx⟩
    centralizer ({pi xM} : Set (M ⧸ A.subgroupOf M)) ≤
      ((residualPairStabilizer M t).subgroupOf M).map pi := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let : IsElementaryAbelian 2 A := d.distinguished_elementary_card.1
  let : IsElementaryAbelian 2 (A.subgroupOf M) :=
    IsElementaryAbelian.subgroupOf distinguishedClosure_le
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  let xM : M := ⟨x, (show residualCommutator M t ≤ M by rw [d.torus_eq_local_pair]; exact inf_le_left.trans inf_le_left) hx⟩
  have hodd : Odd (orderOf xM) := by
    rw [← orderOf_submonoid xM]
    apply Odd.of_dvd_nat ?_ ((residualCommutator M t).orderOf_dvd_natCard hx)
    rw [d.torus_card]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero even_two (by omega : 2 * m + 1 ≠ 0)) odd_one
  have hcop : Nat.Coprime (orderOf xM) (Nat.card (A.subgroupOf M)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe distinguishedClosure_le).toEquiv,
      d.distinguished_elementary_card.2]
    exact hodd.coprime_two_right.pow_right _
  change centralizer ({pi xM} : Set (M ⧸ A.subgroupOf M)) ≤ _
  rw [centralizer_quotient_eq _ xM hcop]
  apply map_mono
  intro y hy
  exact d.torus_centralizer_le_pair hsemi hx hx1 ⟨y.property,
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp hy))⟩

public theorem LocalGeometry.S_inf_pair
    (g : LocalGeometry Z M z t m) :
    g.S ⊓ residualPairStabilizer M t = g.U := by
  obtain ⟨V, hV⟩ := g.U_sylow_pair
  obtain ⟨W, hW⟩ := g.S_sylow
  have hS : IsPGroup 2 g.S := by rw [← hW]; exact W.isPGroup'.map _
  have hU : g.U ≤ residualPairStabilizer M t := by
    rw [← hV]; exact map_subtype_le _
  let R := g.S.subgroupOf (residualPairStabilizer M t)
  let i : R →* g.S :=
    { toFun := fun r => ⟨r, r.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hR : IsPGroup 2 R := hS.of_injective i (fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun u : g.S => (u : G)) h)))
  have hVR : (V : Subgroup (residualPairStabilizer M t)) ≤ R := by
    intro v hv
    exact g.U_le_S (hV ▸ mem_map_of_mem _ hv)
  have he : R = V := V.is_maximal' hR hVR
  apply le_antisymm
  · intro x hx
    exact hV ▸ mem_map_of_mem (residualPairStabilizer M t).subtype
      (show (⟨x, hx.2⟩ : residualPairStabilizer M t) ∈ (V : Subgroup _) from he ▸ hx.1)
  · exact le_inf g.U_le_S hU

public theorem Context.torus_le_normalizer_T (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    residualCommutator M t ≤ normalizer (g.T : Set G) := by
  let B := M ⊓ residualGenerated M z t
  have hKB : residualCommutator M t ≤ B := by
    rw [d.torus_eq_local_pair]
    exact inf_le_inf inf_le_left le_rfl
  have hKP : residualCommutator M t ≤ normalizer (borelTwoCore M z t : Set G) := by
    intro k hk
    apply (pCore 2 B).le_normalizer_map B.subtype
    refine ⟨⟨k, hKB hk⟩, ?_, rfl⟩
    rw [(pCore 2 B).normalizer_eq_top]
    trivial
  have hKU : residualCommutator M t ≤ centralizer (g.U : Set G) := by
    intro k hk u hu
    exact (g.U_le_centralizer hu k (hKB hk).2).symm
  apply le_normalizer_iff.mpr
  intro k hk x hx
  rw [show x ∈ g.T ↔ x ∈ (borelTwoCore M z t : Set G) * (g.U : Set G) from
    Set.ext_iff.mp g.T_product x] at hx
  obtain ⟨p, hp, u, hu, rfl⟩ := hx
  have hpe := (mem_normalizer_iff.mp (hKP hk) p).mp hp
  have hue := (mem_normalizer_iff.mp (Subgroup.centralizer_le_normalizer _ (hKU hk)) u).mp hu
  have hm : k * (p * u) * k⁻¹ = (k * p * k⁻¹) * (k * u * k⁻¹) := by group
  rw [hm]
  exact Set.ext_iff.mp g.T_product _ |>.mpr ⟨_, hpe, _, hue, rfl⟩

public theorem Context.torus_le_normalizer_S (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    residualCommutator M t ≤ normalizer (g.S : Set G) := by
  have hSN : g.S ≤ normalizer (g.T : Set G) := by
    obtain ⟨V, hV⟩ := g.S_sylow
    rw [← hV]
    exact map_subtype_le _
  exact (d.torus_le_normalizer_T g).trans
    ((normal_subgroupOf_iff_le_normalizer hSN).mp s.S_normal)

/-- The literal normalizer in M/A is the image of the normalizer in M. -/
public theorem Context.quotient_sylow_normalizer (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    let A := closure (Z ∩ (M : Set G))
    letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' (A.subgroupOf M)
    (normalizer (g.S.subgroupOf M : Set M)).map pi =
      normalizer ((g.S.subgroupOf M).map pi : Set (M ⧸ A.subgroupOf M)) := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  apply map_normalizer_of_ker_le _ (QuotientGroup.mk'_surjective _) _
  rw [QuotientGroup.ker_mk']
  exact subgroupOf_mono M g.closure_le_S

/-- Equation (14G), with the normalizer and all three images in M/A. -/
public theorem Context.quotient_normalizer_torus_centralizer (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    {x : G} (hx : x ∈ residualCommutator M t) (hx1 : x ≠ 1) :
    let A := closure (Z ∩ (M : Set G))
    letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' (A.subgroupOf M)
    let xM : M := ⟨x, (show residualCommutator M t ≤ M by
      rw [d.torus_eq_local_pair]; exact inf_le_left.trans inf_le_left) hx⟩
    let N := normalizer (g.S.subgroupOf M : Set M)
    let D := (residualPairStabilizer M t).subgroupOf M
    N.map pi ⊓ centralizer ({pi xM} : Set (M ⧸ A.subgroupOf M)) ≤ (N ⊓ D).map pi ∧
      (N ⊓ D).map pi ≤
        (N ⊓ normalizer ((residualCommutator M t).subgroupOf M : Set M)).map pi := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  let N := normalizer (g.S.subgroupOf M : Set M)
  let D := (residualPairStabilizer M t).subgroupOf M
  constructor
  · rw [map_inf_of_ker_le pi N D (by
      rw [QuotientGroup.ker_mk']
      exact (subgroupOf_mono M g.closure_le_S).trans (g.S.subgroupOf M).le_normalizer)]
    exact inf_le_inf_left _ (d.quotient_torus_centralizer_le_pair hsemi hx hx1)
  · apply map_mono
    intro y hy
    exact ⟨hy.1, le_normalizer_comap M.subtype (d.pair_normalizes_torus hy.2)⟩

/-- Every nonidentity torus element fixes exactly U-bar in S-bar. -/
public theorem Context.quotient_sylow_torus_centralizer (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hsemi : TorusSemiregular M t)
    {x : G} (hx : x ∈ residualCommutator M t) (hx1 : x ≠ 1) :
    let A := closure (Z ∩ (M : Set G))
    letI : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' (A.subgroupOf M)
    let xM : M := ⟨x, (show residualCommutator M t ≤ M by
      rw [d.torus_eq_local_pair]; exact inf_le_left.trans inf_le_left) hx⟩
    (g.S.subgroupOf M).map pi ⊓ centralizer ({pi xM} : Set (M ⧸ A.subgroupOf M)) =
      (g.U.subgroupOf M).map pi := by
  let A := closure (Z ∩ (M : Set G))
  let : (A.subgroupOf M).Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' (A.subgroupOf M)
  let xM : M := ⟨x, (show residualCommutator M t ≤ M by
    rw [d.torus_eq_local_pair]; exact inf_le_left.trans inf_le_left) hx⟩
  change (g.S.subgroupOf M).map pi ⊓ centralizer ({pi xM} : Set _) = _
  apply le_antisymm
  · have h := inf_le_inf_left ((g.S.subgroupOf M).map pi)
      (d.quotient_torus_centralizer_le_pair hsemi hx hx1)
    rw [← map_inf_of_ker_le pi (g.S.subgroupOf M)
      ((residualPairStabilizer M t).subgroupOf M) (by
        rw [QuotientGroup.ker_mk']; exact subgroupOf_mono M g.closure_le_S)] at h
    have he : g.S.subgroupOf M ⊓ (residualPairStabilizer M t).subgroupOf M =
        g.U.subgroupOf M := by
      change (g.S ⊓ residualPairStabilizer M t).comap M.subtype = _
      rw [g.S_inf_pair]
      rfl
    rwa [he] at h
  · refine le_inf (map_mono (subgroupOf_mono M g.U_le_S)) ?_
    rintro y ⟨u, hu, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change pi u * pi xM = pi xM * pi u
    rw [← map_mul, ← map_mul]
    apply congrArg pi
    apply Subtype.ext
    exact (g.U_le_centralizer hu x (show x ∈ residualGenerated M z t from
      (d.torus_eq_local_pair ▸ hx).2)).symm

end BenderSuzuki.ZD.SuzukiExclusion
