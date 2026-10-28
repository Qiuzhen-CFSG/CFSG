module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Semilinear
public import Theory.GroupTheory.Recognition.QuasithinM23.ScalarCubicNormalizer
/-!
# The original scalar cubic and its normalizer inside M

The source semilinear equivalence retains both L/O₂(L) and the complete
O₂(M) action. Lift the scalar cubic through that quotient. Its fixed-point-
free action makes its normalizer inside M a complement to O₂(M), and the
original quotient map identifies this normalizer with ΓL₂(4). Transporting
the scalar commutant back through the same quotient marking proves that
the chosen cubic is a Sylow three-subgroup of the literal preimage of
C_{M/O₂(M)}(L/O₂(L)).

This proves the local-normalizer step at the start of Aschbacher–Smith
5.2.15, printed pp.654–655 (`refs/quasithin.pdf`), from the original
nonmaximal linear setup in both orientations. Equality with the normalizer
in G and ambient M₂₃ recognition are further source obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.SL2FourNatural Representation.SL2FourNatural.SemilinearNormalizer
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
theorem Preparation.linear_nonmaximal_scalar_cubic_local_normalizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    let M := normalizer (L : Set G)
    let π := QuotientGroup.mk' (pCore 2 M)
    let Lbar := (L.subgroupOf M).map π
    ∃ e : (M ⧸ pCore 2 M) ≃* Gamma,
      (L.subgroupOf M).map (e.toMonoidHom.comp π) = special.range ∧
      ∃ C : Subgroup M, C.map (e.toMonoidHom.comp π) = scalar.range ∧ Nat.card C = 3 ∧
        (∃ P : Sylow 3 ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π),
          (P : Subgroup ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π)).map
            ((centralizer (Lbar : Set (M ⧸ pCore 2 M))).comap π).subtype = C) ∧
        (pCore 2 M).IsComplement' (Subgroup.normalizer (C : Set M)) ∧
        ∃ eN : Subgroup.normalizer (C : Set M) ≃* Gamma,
          ∀ x : Subgroup.normalizer (C : Set M), eN x = e (π x) := by
  let M := normalizer (L : Set G)
  let π := QuotientGroup.mk' (pCore 2 M)
  obtain ⟨e,he,b,hb⟩ := d.linear_nonmaximal_semilinear_quotient h hH hp E hm hE he hnonmax
  let q := e.toMonoidHom.comp π
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 M :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  let : IsElementaryAbelian 2 (pCore 2 M) := IsElementaryAbelian.of_surjective b.toMonoidHom b.surjective
  have hcard : Nat.card (pCore 2 M) = 16 :=
    (Nat.card_congr b.symm.toEquiv).trans ((Nat.card_congr Multiplicative.toAdd).trans
      ((Nat.card_eq_fintype_card).trans card_vector))
  obtain ⟨C,hC,hCcard,hcomplement,eN,heN,P,hP⟩ :=
    QuasithinM23.exists_scalar_cubic_normalizer (pCore 2 M) hcard q hq hk b hb
  have hD : (centralizer (special.range : Set Gamma)).comap q =
      (centralizer ((L.subgroupOf M).map π : Set (M ⧸ pCore 2 M))).comap π := by
    rw [←he]
    ext x
    constructor
    · intro hx y hy
      obtain ⟨k,hk,rfl⟩ := hy
      apply e.injective
      simpa only [q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul] using hx (q k) (mem_map_of_mem q hk)
    · intro hx y hy
      obtain ⟨k,hk,rfl⟩ := hy
      have hh := congrArg e (hx (π k) (mem_map_of_mem π hk))
      simpa only [q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul] using hh
  refine ⟨e,he,C,hC,hCcard,?_,hcomplement,eN,heN⟩
  have hh : ∃ P : Sylow 3 ((centralizer (special.range : Set Gamma)).comap q),
      (P : Subgroup ((centralizer (special.range : Set Gamma)).comap q)).map
        ((centralizer (special.range : Set Gamma)).comap q).subtype = C := ⟨P,hP⟩
  exact hD ▸ hh
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
