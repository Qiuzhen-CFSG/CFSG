module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.ChiefModules.Quotients
/-!
# Equivariance of the two lift factors

Displacement commutes with K because K centralizes i. Inner U acts trivially
on the central quotient, so the identity extends to P = K U. Consequently
both literal quotient isomorphisms intertwine ambient conjugation with the
selected binary A₅ action. Each action descends to the literal actor quotient.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.MovedCoreModel
variable {G : Type*} [Group G]
variable {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
variable [IsExtraspecial 2 U] (m : MovedCoreModel U K i hKU)

lemma inner_action (u : U) (v : U ⧸ center U) :
    m.action (inclusion (le_sup_right : U ≤ K ⊔ U) u) v = v := by
  let _ := IsExtraspecial.quotient_elementary_abelian 2 U
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (center U) v
  rw [m.formula]
  change QuotientGroup.mk' (center U) (u * w * u⁻¹) = _
  simp [mul_comm]

lemma displacement_equivariant_K
    (hiU : i ∈ normalizer (U : Set G)) (hKi : K ≤ centralizer ({i} : Set G))
    (k : K) (u : U) :
    let _ := IsExtraspecial.quotient_elementary_abelian 2 U
    cyclicDisplacement U (QuotientGroup.mk' (center U)) i hiU
      (normalizingConjugation U k (hKU k.property) u) =
      m.action (inclusion (le_sup_left : K ≤ K ⊔ U) k)
        (cyclicDisplacement U (QuotientGroup.mk' (center U)) i hiU u) := by
  let _ := IsExtraspecial.quotient_elementary_abelian 2 U
  let q := QuotientGroup.mk' (center U)
  have hc : (k : G) * i = i * k := mem_centralizer_singleton_iff.mp (hKi k.property)
  have he : normalizingConjugation U i hiU
      (normalizingConjugation U k (hKU k.property) u) =
      normalizingConjugation U k (hKU k.property)
        (normalizingConjugation U i hiU u) := by
    apply Subtype.ext
    change i * ((k : G) * (u : G) * (k : G)⁻¹) * i⁻¹ =
      (k : G) * (i * (u : G) * i⁻¹) * (k : G)⁻¹
    calc
      _ = (i * k) * (u : G) * (i * k)⁻¹ := by group
      _ = (k * i) * (u : G) * (k * i)⁻¹ := by rw [hc]
      _ = _ := by group
  change q _ * (q _)⁻¹ = m.action _ (q u * (q _)⁻¹)
  rw [map_mul,map_inv,m.formula,m.formula]
  rw [he]
  rfl

lemma displacement_equivariant
    (hiU : i ∈ normalizer (U : Set G)) (hKi : K ≤ centralizer ({i} : Set G))
    (p : ↥(K ⊔ U)) (u : U) :
    let _ := IsExtraspecial.quotient_elementary_abelian 2 U
    cyclicDisplacement U (QuotientGroup.mk' (center U)) i hiU
      (normalizingConjugation U p ((sup_le hKU U.le_normalizer) p.property) u) =
      m.action p (cyclicDisplacement U (QuotientGroup.mk' (center U)) i hiU u) := by
  let _ := IsExtraspecial.quotient_elementary_abelian 2 U
  let f := cyclicDisplacement U (QuotientGroup.mk' (center U)) i hiU
  have hp : (p : G) ∈ (U : Set G) * (K : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U K hKU, sup_comm]
    exact p.property
  obtain ⟨v,hv,k,hk,hvk⟩ := hp
  let vU : U := ⟨v,hv⟩
  let kK : K := ⟨k,hk⟩
  have he : p = inclusion (le_sup_right : U ≤ K ⊔ U) vU *
      inclusion (le_sup_left : K ≤ K ⊔ U) kK := Subtype.ext hvk.symm
  have hconj : normalizingConjugation U p ((sup_le hKU U.le_normalizer) p.property) u =
      vU * normalizingConjugation U k (hKU hk) u * vU⁻¹ := by
    apply Subtype.ext
    change (p : G) * (u : G) * (p : G)⁻¹ = v * (k * (u : G) * k⁻¹) * v⁻¹
    rw [← hvk]
    group
  change f _ = m.action p (f u)
  rw [hconj,map_mul,map_mul,map_inv]
  rw [show f vU * f (normalizingConjugation U k (hKU hk) u) * (f vU)⁻¹ =
    f (normalizingConjugation U k (hKU hk) u) by simp]
  rw [m.displacement_equivariant_K hiU hKi kK u,he,map_mul]
  exact (m.inner_action vU _).symm
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.MovedCoreModel

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G]

/-- An identification of a literal conjugation quotient with the binary core,
including its actual action and its representative formula. -/
structure BinaryFactorModel (P V N : Subgroup G)
    (π : P →* alternatingGroup (Fin 5))
    (hPV : P ≤ normalizer (V : Set G)) [hN : (N.subgroupOf V).Normal] where
  equiv : (V ⧸ N.subgroupOf V) ≃* Multiplicative (BinaryPermutation.core (Fin 5))
  action : P →* MulAut (V ⧸ N.subgroupOf V)
  formula : ∀ (p : P) (v : V), action p (QuotientGroup.mk' (N.subgroupOf V) v) =
    QuotientGroup.mk' (N.subgroupOf V)
      ⟨(p : G) * (v : G) * (p : G)⁻¹,
        (mem_normalizer_iff.mp (hPV p.property) v).mp v.property⟩
  equivariant : ∀ (p : P) (v : V ⧸ N.subgroupOf V), equiv (action p v) =
    Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (π p).val (equiv v).toAdd)

namespace BinaryFactorModel
variable {P V N : Subgroup G} {π : P →* alternatingGroup (Fin 5)}
variable {hPV : P ≤ normalizer (V : Set G)} [hN : (N.subgroupOf V).Normal]
variable (b : BinaryFactorModel P V N π hPV)

/-- The action factors through precisely the supplied quotient presentation. -/
theorem kernel_le : π.ker ≤ b.action.ker := by
  intro p hp
  apply MonoidHom.mem_ker.mpr
  ext v
  apply b.equiv.injective
  rw [b.equivariant,show π p = 1 from hp]
  simp

/-- The descended action is on the literal actor quotient, not a family tag. -/
@[expose] noncomputable def quotientAction (J : Subgroup P) [J.Normal] (hJ : π.ker = J) :
    (P ⧸ J) →* MulAut (V ⧸ N.subgroupOf V) :=
  QuotientGroup.lift J b.action (hJ ▸ b.kernel_le)

@[simp] theorem quotientAction_mk (J : Subgroup P) [J.Normal] (hJ : π.ker = J) (p : P) :
    b.quotientAction J hJ (QuotientGroup.mk' J p) = b.action p := rfl
end BinaryFactorModel

namespace MovedCoreModel
variable [Finite G] {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
variable [IsExtraspecial 2 U] (m : MovedCoreModel U K i hKU)
include m

/-- The A/Z chief factor, with its actual P/U action. -/
theorem base_binary_factor (z : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hmoved : Nat.card (movedImage U i) = 16)
    (hPA : K ⊔ U ≤ normalizer (liftBase U z i : Set G))
    (hPZ : K ⊔ U ≤ normalizer (zpowers z : Set G))
    (hN : ((zpowers z).subgroupOf (liftBase U z i)).Normal) :
    let _ := hN
    Nonempty (BinaryFactorModel (K ⊔ U) (liftBase U z i) (zpowers z) m.π hPA) := by
  let _ := hN
  obtain ⟨e,he⟩ := liftBase_quotient_equiv_moved U z i hZ hiU hmoved hN
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action (K ⊔ U) (liftBase U z i)
    (zpowers z) hPA hPZ hN
  refine ⟨⟨e.trans m.equiv,ρ,hρ,?_⟩⟩
  intro p v
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective ((zpowers z).subgroupOf (liftBase U z i)) v
  rw [hρ]
  change m.equiv (e _) = _
  have hh : e (QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i))
      ⟨(p : G) * (a : G) * (p : G)⁻¹,
        (mem_normalizer_iff.mp (hPA p.property) a).mp a.property⟩) =
      ⟨m.action p (e (QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i)) a)),
        m.invariant p _ (e _).property⟩ := by
    apply Subtype.ext
    dsimp only [Subtype.coe_mk]
    rw [he,he,m.formula]
  rw [hh,m.equivariant]
  rfl

/-- Displacement constructs the U/A binary module with its actual P/U action. -/
theorem core_binary_factor (z : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hKi : K ≤ centralizer ({i} : Set G))
    (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (movedImage U i) = 16)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hPA : K ⊔ U ≤ normalizer (liftBase U z i : Set G))
    (hN : ((liftBase U z i).subgroupOf U).Normal) :
    let _ := hN
    Nonempty (BinaryFactorModel (K ⊔ U) U (liftBase U z i) m.π
      (sup_le hKU U.le_normalizer)) := by
  let _ := hN
  let _ := IsExtraspecial.quotient_elementary_abelian 2 U
  obtain ⟨e,he⟩ := core_quotient_equiv_moved U z i hZ hiU hUcard hmoved hD hN
  have he' (u : U) : (e (QuotientGroup.mk' ((liftBase U z i).subgroupOf U) u) : U ⧸ center U) =
      cyclicDisplacement U (QuotientGroup.mk' (center U)) i hiU u :=
    (he u).trans (cyclicDisplacement_apply U (QuotientGroup.mk' (center U)) i hiU u).symm
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action (K ⊔ U) U
    (liftBase U z i) (sup_le hKU U.le_normalizer) hPA hN
  refine ⟨⟨e.trans m.equiv,ρ,hρ,?_⟩⟩
  intro p v
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective ((liftBase U z i).subgroupOf U) v
  rw [hρ]
  change m.equiv (e _) = _
  have hh : e (QuotientGroup.mk' ((liftBase U z i).subgroupOf U)
      (normalizingConjugation U p ((sup_le hKU U.le_normalizer) p.property) u)) =
      ⟨m.action p (e (QuotientGroup.mk' ((liftBase U z i).subgroupOf U) u)),
        m.invariant p _ (e _).property⟩ := by
    apply Subtype.ext
    dsimp only [Subtype.coe_mk]
    rw [he',he']
    exact m.displacement_equivariant hiU hKi p u
  change m.equiv (e (QuotientGroup.mk' ((liftBase U z i).subgroupOf U)
    (normalizingConjugation U p ((sup_le hKU U.le_normalizer) p.property) u))) = _
  rw [hh,m.equivariant]
  rfl
end MovedCoreModel

namespace MovedCoreModel
variable {U K : Subgroup G} {i : G} {hKU : K ≤ normalizer (U : Set G)}
variable (m : MovedCoreModel U K i hKU)

/-- Either constructed binary factor has an explicit action of the literal
actor quotient P/U, identified with A₅ by the selected quotient isomorphism. -/
theorem quotient_actor_action (V N : Subgroup G)
    (hPV : K ⊔ U ≤ normalizer (V : Set G)) [hN : (N.subgroupOf V).Normal]
    (b : BinaryFactorModel (K ⊔ U) V N m.π hPV) :
    let _ := normal_subgroupOf_of_le_normalizer (sup_le hKU U.le_normalizer)
    ∃ ψ : (↥(K ⊔ U) ⧸ U.subgroupOf (K ⊔ U)) →* MulAut (V ⧸ N.subgroupOf V),
      (∀ (p : ↥(K ⊔ U)) (v : V),
        ψ (QuotientGroup.mk' (U.subgroupOf (K ⊔ U)) p)
          (QuotientGroup.mk' (N.subgroupOf V) v) =
          QuotientGroup.mk' (N.subgroupOf V) ⟨(p : G) * (v : G) * (p : G)⁻¹,
            (mem_normalizer_iff.mp (hPV p.property) v).mp v.property⟩) ∧
      (∀ (p : ↥(K ⊔ U) ⧸ U.subgroupOf (K ⊔ U)) (v : V ⧸ N.subgroupOf V),
        b.equiv (ψ p v) = Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (m.actorEquiv p).val (b.equiv v).toAdd)) := by
  let _ := normal_subgroupOf_of_le_normalizer (sup_le hKU U.le_normalizer)
  refine ⟨b.quotientAction (U.subgroupOf (K ⊔ U)) m.kernel,?_,?_⟩
  · intro p v
    rw [b.quotientAction_mk]
    exact b.formula p v
  · intro p v
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (K ⊔ U)) p
    rw [b.quotientAction_mk,m.actorEquiv_mk]
    exact b.equivariant p v
end MovedCoreModel

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
