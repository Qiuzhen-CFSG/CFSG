module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Setup
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Algebra

/-!
# The terminal elementary-sixteen construction in the A₆ shadow

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.569–570, following Lemma 2.5.27.

The incoming source setup yields a normal cyclic four-group in `S_C`.
The distinct center lines imply that `S_K` and `S_Kˣ` are disjoint and commute.
Thus each Klein four-group in `S_K` gives an actual elementary abelian product
of order sixteen, containing `z` when the four-group contains `zK`.

The remaining Aut(A₆) image calculation must force `S_C = C₄`. The choice of
the four-group stable under `x²` and the full normalizer calculation must still
supply the terminal local pair and its order. None is asserted here as a
completed source theorem.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction

open Subgroup

variable {G : Type*} [Group G]

/-- The centralizer factor `S_C = C_S(K)`. -/
@[expose] public def Setup.core (d : Setup G) : Subgroup G :=
  d.S ⊓ centralizer (d.K : Set G)

/-- The Sylow subgroup `S_K = S ∩ K`. -/
@[expose] public def Setup.sk (d : Setup G) : Subgroup G := d.S ⊓ d.K

private theorem s_le_h (d : Setup G) : d.S ≤ d.H := by
  rw [d.generated]
  exact le_sup_right

private theorem k_le_h (d : Setup G) : d.K ≤ d.H := by
  rw [d.generated]
  exact le_sup_left

private theorem two_s (d : Setup G) : IsPGroup 2 d.S :=
  d.twoT.of_injective (inclusion d.s_le_t) (inclusion_injective _)

private theorem normal_core (d : Setup G) : (d.core.subgroupOf d.S).Normal := by
  have hCH : d.core ≤ d.H := inf_le_left.trans (s_le_h d)
  have hn : (d.core.subgroupOf d.H).Normal := by
    change ((d.S ⊓ centralizer (d.K : Set G)).subgroupOf d.H).Normal
    rw [← d.action_kernel]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    ((s_le_h d).trans ((normal_subgroupOf_iff_le_normalizer hCH).mp hn))

/-- Extract the normal cyclic four-group in the actual `S_C`, preserving
normality inside `S`. This uses the incoming conclusion of 2.5.27. -/
public theorem Setup.exists_normal_cyclicFour [Finite G] (d : Setup G) :
    ∃ V : Subgroup G, V ≤ d.core ∧ (V.subgroupOf d.S).Normal ∧
      Nonempty (V ≃* Multiplicative (ZMod 4)) := by
  let : (d.core.subgroupOf d.S).Normal := normal_core d
  let e := subgroupOfEquivOfLe (show d.core ≤ d.S from inf_le_left)
  have hc : Nonempty (d.core.subgroupOf d.S ≃* Multiplicative (ZMod 4)) ∨
      Nonempty (d.core.subgroupOf d.S ≃* Multiplicative (ZMod 8)) ∨
      Nonempty (d.core.subgroupOf d.S ≃* QuaternionGroup 2) := by
    rcases d.alternatives with hf | hf | hf
    · obtain ⟨f⟩ := hf
      exact Or.inl ⟨e.trans f⟩
    · obtain ⟨f⟩ := hf
      exact Or.inr (Or.inl ⟨e.trans f⟩)
    · obtain ⟨f⟩ := hf
      exact Or.inr (Or.inr ⟨e.trans f⟩)
  obtain ⟨V, hn, hVC, ⟨f⟩⟩ := exists_normal_cyclicFour_of_shadow_alternatives
    (two_s d) (d.core.subgroupOf d.S) hc
  refine ⟨V.map d.S.subtype, map_le_iff_le_comap.mpr hVC, ?_,
    ⟨(V.equivMapOfInjective d.S.subtype d.S.subtype_injective).symm.trans f⟩⟩
  change ((V.map d.S.subtype).comap d.S.subtype).Normal
  rwa [V.comap_map_eq_self_of_injective d.S.subtype_injective]

/-- The center relation and `x² ∈ S` give `zKˣ = t`, with right conjugation. -/
public theorem Setup.zK_conjugate (d : Setup G) : d.x⁻¹ * d.zK * d.x = d.t := by
  have htZ : d.t ∈ (center d.S).map d.S.subtype := by
    rw [d.center_s]
    exact mem_sup_left (mem_zpowers d.t)
  obtain ⟨tS, htS, htval⟩ := htZ
  change (tS : G) = d.t at htval
  have htcomm : d.x ^ 2 * d.t = d.t * d.x ^ 2 := by
    have hh := congrArg Subtype.val
      (mem_center_iff.mp htS (⟨d.x ^ 2, d.square_mem⟩ : d.S))
    simpa only [coe_mul, htval] using hh
  calc
    d.x⁻¹ * d.zK * d.x = (d.x ^ 2)⁻¹ * (d.t * d.x ^ 2) := by
      rw [← d.t_conjugate]
      simp only [pow_two]
      group
    _ = d.t := by rw [← htcomm]; group

private theorem normal_sk (d : Setup G) : (d.sk.subgroupOf d.S).Normal := by
  have hHK : d.H ≤ normalizer (d.K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (k_le_h d)).mp d.normalK
  unfold Setup.sk
  rw [inf_subgroupOf_left]
  apply normal_subgroupOf_of_le_normalizer
  exact (s_le_h d).trans hHK

private theorem normal_conjugate (S D : Subgroup G) (hDS : D ≤ S)
    (hD : (D.subgroupOf S).Normal) {x : G} (hx : x ∈ normalizer (S : Set G)) :
    (conjugate x D).subgroupOf S |>.Normal := by
  have hS : conjugate x S = S :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (S : Set G)).inv_mem hx)
  have hDX : conjugate x D ≤ S := hS ▸ map_mono hDS
  apply (normal_subgroupOf_iff_le_normalizer hDX).mpr
  have hSN : S ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDS).mp hD
  calc
    S = conjugate x S := hS.symm
    _ ≤ (normalizer (D : Set G)).map (MulAut.conj x⁻¹).toMonoidHom := map_mono hSN
    _ ≤ normalizer (conjugate x D : Set G) := le_normalizer_map _

private theorem relative_disjoint_of_centers [Finite G]
    (S D F : Subgroup G) (hS : IsPGroup 2 S)
    (hDS : D ≤ S) (hFS : F ≤ S)
    (hD : (D.subgroupOf S).Normal) (hF : (F.subgroupOf S).Normal)
    (hc : Disjoint ((center D).map D.subtype) ((center F).map F.subtype)) :
    Disjoint D F := by
  let : (D.subgroupOf S).Normal := hD
  let : (F.subgroupOf S).Normal := hF
  have hi : D.subgroupOf S ⊓ F.subgroupOf S = ⊥ := by
    by_contra hn
    apply center_inf_ne_bot_of_normal hS (D.subgroupOf S ⊓ F.subgroupOf S) hn
    apply bot_unique
    rintro g ⟨hgZ, hgD, hgF⟩
    have hgDC : (g : G) ∈ (center D).map D.subtype := by
      refine ⟨⟨g, hgD⟩, mem_center_iff.mpr ?_, rfl⟩
      intro a
      apply Subtype.ext
      exact congrArg (fun s : S => (s : G))
        (mem_center_iff.mp hgZ (⟨a, hDS a.property⟩ : S))
    have hgFC : (g : G) ∈ (center F).map F.subtype := by
      refine ⟨⟨g, hgF⟩, mem_center_iff.mpr ?_, rfl⟩
      intro a
      apply Subtype.ext
      exact congrArg (fun s : S => (s : G))
        (mem_center_iff.mp hgZ (⟨a, hFS a.property⟩ : S))
    exact Subtype.ext (disjoint_def.mp hc hgDC hgFC)
  apply disjoint_def.mpr
  intro g hgD hgF
  have hg : (⟨g, hDS hgD⟩ : S) ∈ D.subgroupOf S ⊓ F.subgroupOf S := ⟨hgD, hgF⟩
  rw [hi, mem_bot] at hg
  exact congrArg Subtype.val hg

/-- The two copies of `S_K` are disjoint. Normality is used only within `S`,
and the distinct center lines come from 2.5.5 and 2.5.11–13, 2.5.25. -/
public theorem Setup.disjoint_sk_conjugate [Finite G] (d : Setup G) :
    Disjoint d.sk (conjugate d.x d.sk) := by
  have hXS : conjugate d.x d.S = d.S :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (d.S : Set G)).inv_mem d.x_normalizes)
  have hDX : conjugate d.x d.sk ≤ d.S := hXS ▸ map_mono inf_le_left
  apply relative_disjoint_of_centers d.S d.sk (conjugate d.x d.sk) (two_s d)
    inf_le_left hDX (normal_sk d) (normal_conjugate d.S d.sk inf_le_left (normal_sk d) d.x_normalizes)
  have htC : zpowers d.t ≤ d.core := zpowers_le.mpr d.t_mem
  have hzCX : zpowers d.zK ≤ conjugate d.x d.core := by
    apply zpowers_le.mpr
    exact ⟨d.t, d.t_mem, by simpa using d.t_conjugate⟩
  have hzXt : conjugate d.x (zpowers d.zK) = zpowers d.t := by
    unfold conjugate
    rw [MonoidHom.map_zpowers]
    congr 1
    simpa using d.zK_conjugate
  have hcenterDX : (center (conjugate d.x d.sk)).map (conjugate d.x d.sk).subtype ≤
      zpowers d.t := by
    rintro g ⟨g', hg', rfl⟩
    let e : d.sk ≃* conjugate d.x d.sk := (MulAut.conj d.x⁻¹).subgroupMap d.sk
    have hp : e.symm g' ∈ center d.sk := (centerCongr e.symm ⟨g', hg'⟩).property
    have hz : (e.symm g' : G) ∈ zpowers d.zK := by
      rw [← d.center_sk]
      exact ⟨e.symm g', hp, rfl⟩
    rw [← hzXt]
    refine ⟨e.symm g', hz, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply g')
  have hcenterD : (center d.sk).map d.sk.subtype ≤ conjugate d.x d.core := by
    change (center (d.S ⊓ d.K : Subgroup G)).map (d.S ⊓ d.K).subtype ≤ _
    rw [d.center_sk]
    exact hzCX
  exact d.core_disjoint.symm.mono hcenterD (hcenterDX.trans htC)

/-- The disjoint normal Sylow factors commute in the ambient group. -/
public theorem Setup.sk_centralizes_conjugate [Finite G] (d : Setup G) :
    d.sk ≤ centralizer (conjugate d.x d.sk : Set G) := by
  have hXS : conjugate d.x d.S = d.S :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (d.S : Set G)).inv_mem d.x_normalizes)
  have hDX : conjugate d.x d.sk ≤ d.S := hXS ▸ map_mono inf_le_left
  let : (d.sk.subgroupOf d.S).Normal := normal_sk d
  let : ((conjugate d.x d.sk).subgroupOf d.S).Normal :=
    normal_conjugate d.S d.sk inf_le_left (normal_sk d) d.x_normalizes
  have hdisj : Disjoint (d.sk.subgroupOf d.S) ((conjugate d.x d.sk).subgroupOf d.S) := by
    apply disjoint_def.mpr
    intro s hsD hsF
    exact Subtype.ext (disjoint_def.mp d.disjoint_sk_conjugate hsD hsF)
  have hc := centralizes_of_disjoint_normal (d.sk.subgroupOf d.S)
    ((conjugate d.x d.sk).subgroupOf d.S) hdisj
  intro g hg f hf
  exact congrArg Subtype.val
    (hc (show (⟨g, hg.1⟩ : d.S) ∈ d.sk.subgroupOf d.S from hg)
      (⟨f, hDX hf⟩ : d.S) hf)

/-- Every Klein four-group in `S_K` gives the elementary-sixteen product.
The normalizer and square-stability calculations remain separate. -/
public theorem Setup.elementarySixteen [Finite G] (d : Setup G)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk) :
    Nonempty ((E ⊔ conjugate d.x E : Subgroup G) ≃* E × E) ∧
      IsElementaryAbelian 2 (E ⊔ conjugate d.x E : Subgroup G) ∧
      Nat.card (E ⊔ conjugate d.x E : Subgroup G) = 16 := by
  have hEX : conjugate d.x E ≤ conjugate d.x d.sk := map_mono hE
  exact elementarySixteen_of_disjoint_conjugates E d.x
    (d.disjoint_sk_conjugate.mono hE hEX)
    (fun _ hg _ hf => d.sk_centralizes_conjugate (hE hg) _ (hEX hf))

/-- The product contains the distinguished involution when the chosen four-group
contains the central involution of `S_K`. -/
public theorem Setup.z_mem_product (d : Setup G) (E : Subgroup G)
    (hzK : d.zK ∈ E) : d.z ∈ E ⊔ conjugate d.x E :=
  product_involution_mem_join E hzK d.zK_conjugate d.z_eq

/-- Output required from the Aut(A₆) image calculation. This is an intermediate
result to be proved, not an additional source hypothesis. A downstream
conditional proof may use it; final assembly must construct it. -/
public structure CoreReduction (d : Setup G) where
  cyclic : Nonempty (d.core ≃* Multiplicative (ZMod 4))
  card_s : Nat.card d.S = 128
  inverts : ∀ (E : Subgroup G), E ≤ d.sk → IsKleinFour E →
    ∀ e ∈ E, e ∉ zpowers d.zK → ∀ v ∈ d.core,
      (d.x⁻¹ * e * d.x)⁻¹ * v * (d.x⁻¹ * e * d.x) = v⁻¹

/-- Output required from the ambient normalizer calculation after the cyclic
core reduction. Every subgroup in the assertions is the actual source
subgroup. This record is a proof target, not a replacement for that calculation. -/
public structure NormalizerGeometry (d : Setup G) where
  E : Subgroup G
  four : IsKleinFour E
  le_sk : E ≤ d.sk
  zK_mem : d.zK ∈ E
  e : G
  e_mem : e ∈ E
  e_outside : e ∉ zpowers d.zK
  square_normalizes : d.x ^ 2 ∈ normalizer (E : Set G)
  same_normalizer :
    d.H ⊓ normalizer ((E ⊔ conjugate d.x E : Subgroup G) : Set G) =
      d.H ⊓ normalizer (E : Set G)
  product_normalizer :
    d.H ⊓ normalizer ((E ⊔ conjugate d.x E : Subgroup G) : Set G) =
      (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) ⊔ (d.K ⊓ normalizer (E : Set G))
  factors_disjoint : Disjoint (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core)
    (d.K ⊓ normalizer (E : Set G))
  factors_commute : (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) ≤
    centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G)
  dihedral : Nonempty ((zpowers (d.x⁻¹ * e * d.x) ⊔ d.core : Subgroup G) ≃*
    DihedralGroup 4)
  symmetric : Nonempty ((d.K ⊓ normalizer (E : Set G) : Subgroup G) ≃* Equiv.Perm (Fin 4))
  card_base : Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) = 64

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
