module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalResidual
public import Theory.GroupTheory.Amalgam.DihedralTwelvePair
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupAction.TwoOrbitInnerAction
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.Injective

/-!
# The cubic-residual alternative of Goldschmidt (2.14)

When the two-residual is cubic, it centralizes the two-core. The Sylow
Frattini subgroup lies in that core, so it is normal in the whole group;
the original characteristic obstruction makes it trivial. Thus the Sylow
is elementary. Split its core as a vector-space summand, and extend the
projection through the normal cubic complement. This constructs the actual
direct-product isomorphism with S₃ times the elementary two-core.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.14)(a),
printed pp.384--385.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] [Finite G]

private theorem core_relIndex_sylow
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G) :
    (pCore 2 G).relIndex (P : Subgroup G) = 2 := by
  have hh := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal P)
  rw [SymmetricThreeTwoCore.sylow_index_three e P,
    SymmetricThreeTwoCore.core_index e] at hh
  omega

/-- In the cubic-residual branch, the given Sylow subgroup is elementary. -/
theorem local_sylow_elementary_of_cubic
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal)
    (hr : Nat.card (pResidual 2 G) = 3) : IsElementaryAbelian 2 P := by
  let Q := pCore 2 G
  let R := pResidual 2 G
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card R) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hr, hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hRQ : R ≤ centralizer (Q : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hcop.symm))
  have hφQ : frattini P ≤ Q.subgroupOf (P : Subgroup G) :=
    frattini_le_of_index_dvd_two_source _ (by
      change (pCore 2 G).relIndex (P : Subgroup G) ∣ 2
      rw [core_relIndex_sylow e P])
  let K := (frattini P).map (P : Subgroup G).subtype
  have hKQ : K ≤ Q := map_le_iff_le_comap.mpr hφQ
  have hPK : (P : Subgroup G) ≤ normalizer (K : Set G) := by
    have hh := (frattini P).le_normalizer_map (P : Subgroup G).subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hRK : R ≤ normalizer (K : Set G) :=
    (hRQ.trans (centralizer_le hKQ)).trans (Subgroup.centralizer_le_normalizer _)
  have hKN : K.Normal := normalizer_eq_top_iff.mp
    (top_unique ((pResidual_sup_sylow_eq_top P).symm.le.trans (sup_le hRK hPK)))
  have hφ : frattini P = ⊥ := by
    by_contra hn
    exact hP _ inferInstance hn hKN
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hφ

/-- The cubic-residual case is the literal elementary-core product S₃×O₂(G). -/
theorem local_product_of_cubic
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) (P : Sylow 2 G)
    (hP : ∀ K : Subgroup P, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (P : Subgroup G).subtype).Normal)
    (hr : Nat.card (pResidual 2 G) = 3) :
    IsElementaryAbelian 2 (pCore 2 G) ∧
      Nonempty (G ≃* Equiv.Perm (Fin 3) × pCore 2 G) := by
  let Q := pCore 2 G
  let QP := Q.subgroupOf (P : Subgroup G)
  have hQP : Q ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  let u : QP ≃* Q := subgroupOfEquivOfLe hQP
  let : IsElementaryAbelian 2 P := local_sylow_elementary_of_cubic e P hP hr
  have hQ : IsElementaryAbelian 2 Q :=
    IsElementaryAbelian.of_injective (Subgroup.inclusion hQP)
      (Subgroup.inclusion_injective hQP)
  refine ⟨hQ, ?_⟩
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 P QP
  obtain ⟨v, hv⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting QP C hC.disjoint
    (by intro a ha b hb; exact IsMulCommutative.is_comm.comm _ _)
  let v' : QP × C ≃* P := v.trans ((MulEquiv.subgroupCongr hC.sup_eq_top).trans topEquiv)
  let rP : P →* Q := u.toMonoidHom.comp ((MonoidHom.fst QP C).comp v'.symm.toMonoidHom)
  have hrP (q : QP) : rP q = u q := by
    have hvq : v' (q, 1) = q := by
      exact (hv q 1).trans (mul_one _)
    change u (v'.symm q).1 = u q
    rw [← hvq, v'.symm_apply_apply]
  obtain ⟨r, hr'⟩ := RankTwoAmalgam.retraction_of_normal_complement_card
    (P : Subgroup G).subtype (P : Subgroup G).subtype_injective (pResidual 2 G)
    (by obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
        rw [hr, hn]
        exact (by decide : Nat.Coprime 3 2).pow_right n)
    (by rw [hr, ← (P : Subgroup G).index_mul_card,
      SymmetricThreeTwoCore.sylow_index_three e P])
  let f := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  let m : G →* Equiv.Perm (Fin 3) × Q := f.prod (rP.comp r)
  have hm : Function.Injective m := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro x hx
    have hfx : f x = 1 := congrArg Prod.fst hx
    have hxQ : x ∈ Q := (QuotientGroup.eq_one_iff x).mp
      (e.injective (hfx.trans e.map_one.symm))
    let q : QP := ⟨⟨x, hQP hxQ⟩, hxQ⟩
    have hrx : r x = (q : P) := hr' q
    have hqx : u q = 1 := by
      have hh := congrArg Prod.snd hx
      change rP (r x) = 1 at hh
      rwa [hrx, hrP] at hh
    exact congrArg Subtype.val hqx
  have hc : Nat.card G = Nat.card (Equiv.Perm (Fin 3) × Q) := by
    rw [Nat.card_prod, SymmetricThreeTwoCore.card_eq e]
    congr 1
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact ⟨MulEquiv.ofBijective m ((Nat.bijective_iff_injective_and_card m).mpr ⟨hm, hc⟩)⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
