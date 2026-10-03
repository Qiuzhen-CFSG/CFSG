module
public import Stellmacher.SectionOne.OneSevenSelectedFactorGeneration

/-!
# Sylow transitivity on the canonical one-seven factors

Under the Section 1 module hypotheses, suppose `oneE` together with the Sylow
subgroup generates the group, and the Sylow subgroup has a unique maximal
overgroup. Conjugation by the Sylow subgroup is then transitive on the actual
finite family `oneSevenFactors`. Consequently its cardinality is a power of
two, by the orbit-cardinality theorem for actions of two-groups.

Choose a canonical factor `D` generating with the Sylow subgroup using the
unique-maximal selection theorem, and let `N` be its ambient normal closure.
The quotient by `N` is a two-group because the Sylow subgroup generates it.
The global one-seven product normalizes each canonical factor and is a normal
supplement to the Sylow subgroup, so every ambient conjugate of `D` is a Sylow
conjugate. A factor outside that orbit therefore centralizes `N`, by the
pairwise commutation in the global product. Its intersection with `N` lies in
its own trivial center; consequently it embeds in the two-group quotient.
Its order six rules this out. Every factor thus lies in the selected orbit,
which proves transitivity between arbitrary factors.

This is the canonical-factor orbit argument used with Stellmacher (1.7) in
the local analysis of (9.3), Journal of Algebra 190 (1997), p.50. The argument
uses the production factor family and derives its conjugation behavior; no
permutation or transitivity assumption on an arbitrary family is added.
-/

namespace Stellmacher.SectionOne
universe u
open Subgroup

public theorem oneSeven_factor_orbit_transitive
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hgen : oneE (V := V) (S : Subgroup G) ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    ∀ D ∈ oneSevenFactors (G := G) (V := V),
      ∀ F ∈ oneSevenFactors (G := G) (V := V),
        ∃ s : S, D.conjBy (s : G) = F := by
  classical
  let E := oneSevenGenerated (G := G) (V := V)
  obtain ⟨hEn, hprod, _⟩ := oneSeven_global_product h S
  let _ : E.Normal := hEn
  have hES : E ⊔ (S : Subgroup G) = ⊤ := by
    rwa [(oneSeven_global_identification h S).2] at hgen
  obtain ⟨D, hD, hDS⟩ := oneSeven_exists_factor_sup_sylow_eq_top h S hgen hunique
  have hDE : D ≤ E := le_sSup ((mem_oneSevenFactors_iff D).mp hD)
  have hED : E ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hDE).mp (hprod.2.1 D hD)
  let N := normalClosure (D : Set G)
  let _ : N.Normal := normalClosure_normal
  let q := QuotientGroup.mk' N
  have hDker : D ≤ q.ker := by
    simpa only [q, QuotientGroup.ker_mk'] using (le_normalClosure : D ≤ N)
  have hQp : IsPGroup 2 (G ⧸ N) := by
    have htop : (S : Subgroup G).map q = ⊤ := by
      have hh := congrArg (fun K : Subgroup G => K.map q) hDS
      rw [Subgroup.map_sup, (map_eq_bot_iff D).mpr hDker, bot_sup_eq,
        map_top_of_surjective q (QuotientGroup.mk'_surjective N)] at hh
      exact hh
    have hh := S.isPGroup'.map q
    rw [htop] at hh
    exact hh.of_equiv topEquiv
  have horbit (F : Subgroup G) (hF : F ∈ oneSevenFactors (G := G) (V := V)) :
      ∃ s : S, D.conjBy (s : G) = F := by
    by_contra! hn
    have hcent : N ≤ centralizer (F : Set G) := by
      apply (closure_le _).mpr
      intro x hx
      obtain ⟨d, hd, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
      have hg : g ∈ (S : Subgroup G) ⊔ E := by rw [sup_comm, hES]; trivial
      obtain ⟨s, hs, e, he, rfl⟩ := mem_sup_of_normal_right.mp hg
      have hed : e * d * e⁻¹ ∈ D := (mem_normalizer_iff.mp (hED he) d).mp hd
      have hDconj : D.conjBy s ∈ oneSevenFactors (G := G) (V := V) :=
        (mem_oneSevenFactors_iff _).mpr (((mem_oneSevenFactors_iff D).mp hD).conjBy D s)
      have hcomm := hprod.2.2.2 (D.conjBy s) hDconj F hF (hn ⟨s,hs⟩)
      have hx : (s * e) * d * (s * e)⁻¹ ∈ D.conjBy s := by
        refine ⟨e * d * e⁻¹, hed, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      intro f hf
      exact (hcomm _ hx f hf).symm
    have hinj : Function.Injective (q.comp F.subtype) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply eq_bot_iff.mpr
      intro x hx
      have hxN : (x : G) ∈ N := by
        change q (x : G) = 1 at hx
        exact (QuotientGroup.eq_one_iff _).mp hx
      have hxcenter : x ∈ center F := mem_center_iff.mpr (by
        intro y
        exact Subtype.ext (hcent hxN y y.property))
      rw [RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two
        ((mem_oneSevenFactors_iff F).mp hF).1, mem_bot] at hxcenter
      exact hxcenter
    have hFp : IsPGroup 2 F := hQp.of_injective (q.comp F.subtype) hinj
    obtain ⟨n, hcard⟩ := (IsPGroup.iff_card (p := 2)).mp hFp
    have hthree : 3 ∣ 2 ^ n := by
      rw [← hcard, RankOneThreeGroupAssembly.isSL2Two_card
        ((mem_oneSevenFactors_iff F).mp hF).1]
      norm_num
    have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
    norm_num at this
  intro D1 hD1 D2 hD2
  obtain ⟨s1, hs1⟩ := horbit D1 hD1
  obtain ⟨s2, hs2⟩ := horbit D2 hD2
  refine ⟨s2 * s1⁻¹, ?_⟩
  change D1.conjBy ((s2 : G) * (s1 : G)⁻¹) = D2
  rw [conjBy_mul, ← hs1, conjBy_inv, hs2]

/-- The canonical one-seven factor count is a power of two. -/
public theorem oneSevenFactors_card_eq_two_pow
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hgen : oneE (V := V) (S : Subgroup G) ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    ∃ n : ℕ, (oneSevenFactors (G := G) (V := V)).card = 2 ^ n := by
  classical
  let F := oneSevenFactors (G := G) (V := V)
  let I := {D : Subgroup G // D ∈ F}
  let : MulAction S I := {
    smul := fun s D => ⟨D.val.conjBy (s : G),
      (mem_oneSevenFactors_iff _).mpr
        (((mem_oneSevenFactors_iff D.val).mp D.property).conjBy D.val s)⟩
    one_smul := fun D => Subtype.ext (conjBy_one D.val)
    mul_smul := fun s t D => Subtype.ext (conjBy_mul D.val s t) }
  obtain ⟨D, hD, _⟩ := oneSeven_exists_factor_sup_sylow_eq_top h S hgen hunique
  let d : I := ⟨D,hD⟩
  have hmem (i : I) : i ∈ MulAction.orbit S d := by
    obtain ⟨s, hs⟩ := oneSeven_factor_orbit_transitive h S hgen hunique D hD i i.property
    exact ⟨s, Subtype.ext hs⟩
  let e : MulAction.orbit S d ≃ I := {
    toFun := Subtype.val
    invFun := fun i => ⟨i,hmem i⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  obtain ⟨n, hn⟩ := S.isPGroup'.card_orbit (α := I) d
  refine ⟨n, ?_⟩
  rw [Nat.card_congr e] at hn
  simpa only [I, Nat.card_eq_fintype_card, Fintype.card_coe] using hn

end Stellmacher.SectionOne
