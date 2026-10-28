module

public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Universal property and quotients of the prime residual

For a finite group G, Oᵖ(G) is the least normal subgroup with p-group
quotient. Every homomorphism into a p-group factors uniquely through that
quotient. Under the literal map G → G/N, its image is Oᵖ(G/N) and its
inverse image is Oᵖ(G)N. Restricting the map gives the canonical isomorphism
Oᵖ(G)/(N ∩ Oᵖ(G)) ≃ Oᵖ(G/N); no containment of N in the residual is needed.

The quotient criterion follows by taking a further quotient of the finite
p-group G/Oᵖ(G). The isomorphism is the first isomorphism theorem applied
to the restriction of the quotient map to Oᵖ(G).

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), proof of B.6.8, printed
pp.113–115, with p = 2 and N = J or O₂(H).
-/

public section
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Every homomorphism to a p-group kills the p-residual. -/
theorem pResidual_le_ker_of_isPGroup (p : ℕ) (f : G →* H) (hH : IsPGroup p H) :
    pResidual p G ≤ f.ker := by
  exact sInf_le ⟨inferInstance, (hH.to_subgroup f.range).of_equiv
    (QuotientGroup.quotientKerEquivRange f).symm⟩

/-- Homomorphisms into p-groups factor uniquely through the residual quotient. -/
theorem existsUnique_pResidual_lift (p : ℕ) (f : G →* H) (hH : IsPGroup p H) :
    ∃! g : G ⧸ pResidual p G →* H, g.comp (QuotientGroup.mk' (pResidual p G)) = f := by
  refine ⟨QuotientGroup.lift _ f (pResidual_le_ker_of_isPGroup p f hH), rfl, ?_⟩
  intro g hg
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pResidual p G) x
  exact DFunLike.congr_fun hg y

variable [Finite G]

/-- In a finite group, containing the p-residual is equivalent to having
p-group quotient. Normality refers to N in G. -/
theorem pResidual_le_iff_isPGroup_quotient (p : ℕ) (N : Subgroup G) [N.Normal] :
    pResidual p G ≤ N ↔ IsPGroup p (G ⧸ N) := by
  constructor
  · intro h
    exact (isPGroup_quotient_pResidual p).of_surjective
      (QuotientGroup.map _ N (MonoidHom.id G) h)
      (QuotientGroup.map_surjective_of_surjective _ _ _ QuotientGroup.mk_surjective h)
  · intro h
    exact sInf_le ⟨inferInstance, h⟩

/-- The image of the residual under the actual quotient map is the residual
of the quotient. -/
theorem map_pResidual_quotient (p : ℕ) (N : Subgroup G) [N.Normal] :
    (pResidual p G).map (QuotientGroup.mk' N) = pResidual p (G ⧸ N) :=
  map_pResidual_of_surjective p _ (QuotientGroup.mk'_surjective N)

/-- The inverse image of the quotient's residual is Oᵖ(G)N. -/
theorem comap_pResidual_quotient (p : ℕ) (N : Subgroup G) [N.Normal] :
    (pResidual p (G ⧸ N)).comap (QuotientGroup.mk' N) = pResidual p G ⊔ N := by
  rw [← map_pResidual_quotient p N, comap_map_eq, QuotientGroup.ker_mk']

/-- Restricting G → G/N identifies Oᵖ(G)/(N ∩ Oᵖ(G)) with Oᵖ(G/N).
The kernel is a subgroup of Oᵖ(G), not an assumed inclusion N ≤ Oᵖ(G). -/
noncomputable def pResidualQuotientEquiv (p : ℕ) (N : Subgroup G) [N.Normal] :
    (pResidual p G ⧸ N.subgroupOf (pResidual p G)) ≃* pResidual p (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  let f := q.subgroupMap (pResidual p G)
  have hk : N.subgroupOf (pResidual p G) = f.ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
  exact (QuotientGroup.quotientMulEquivOfEq hk).trans
    ((QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective _)).trans
      (MulEquiv.subgroupCongr (map_pResidual_quotient p N)))

/-- The residual quotient isomorphism is induced by the original quotient map. -/
@[simp] theorem pResidualQuotientEquiv_mk (p : ℕ) (N : Subgroup G) [N.Normal]
    (x : pResidual p G) :
    ((pResidualQuotientEquiv p N (QuotientGroup.mk' (N.subgroupOf (pResidual p G)) x) :
      pResidual p (G ⧸ N)) : G ⧸ N) = QuotientGroup.mk' N x := by
  rfl

end Subgroup
end
