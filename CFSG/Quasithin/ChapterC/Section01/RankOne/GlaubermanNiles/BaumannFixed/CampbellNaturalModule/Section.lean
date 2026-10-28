module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellContainment
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Campbell's normal closure and its natural section

The generalized-Fitting centralizer theorem puts the Sylow omega-center in
Ω₁(Z(O₂(G))). Normality then puts its entire normal closure there. Independently,
the Frattini argument and the no-partial-complement condition in G/O₂(G)
identify the Sylow intersection of the covering kernel with O₂(G).

`NaturalSection` specifies the genuine conjugation action and the quotient
W/C_W(G) occurring in Campbell II.3.2. The source theorem must construct this
data from factorization failure. In particular the natural projection, its
surjectivity and its precise central kernel are not assumed in `Embedding`.

Source: N. R. Campbell, *Pushing up in Finite Groups* (1979), Chapter II
§§2–3, printed pp.23–24, https://thesis.caltech.edu/17847/.
-/

@[expose] public section

open Theory.GroupTheory Stellmacher Subgroup
open Matrix Matrix.SpecialLinearGroup

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell
variable {T G : Type*} [Group T] [Group G] [Finite G]

/-- The literal normal closure W = ⟨Ω₁(Z(S))^G⟩. -/
def Embedding.centerClosure (d : Embedding T G) : Subgroup G :=
  Subgroup.normalClosure (omegaOneCenterAmbient (d.sylow : Subgroup G) : Set G)

instance Embedding.centerClosure_normal (d : Embedding T G) : d.centerClosure.Normal :=
  inferInstanceAs (Subgroup.normalClosure _).Normal

/-- Self-centralization of O₂(G) puts the entire normal closure in its omega-center. -/
theorem Embedding.centerClosure_le_omegaCore (d : Embedding T G) :
    d.centerClosure ≤ omegaOneCenterAmbient (pCore 2 G) := by
  let : (omegaOneCenterAmbient (pCore 2 G)).Normal := omegaCore_normal
  have hQS : pCore 2 G ≤ (d.sylow : Subgroup G) :=
    pCore_isPGroup.le_sylow_of_normal d.sylow
  have hC : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [← d.rankOne.fitting]
    exact centralizer_generalizedFitting_le G
  apply Subgroup.normalClosure_le_normal
  intro x hx
  obtain ⟨_, hx2, hxc⟩ := (mem_omegaOneCenterAmbient_iff _ x).mp hx
  have hxQ : x ∈ centralizer (pCore 2 G : Set G) := fun y hy => hxc y (hQS hy)
  exact (mem_omegaOneCenterAmbient_iff _ x).mpr ⟨hC hxQ, hx2, hxQ⟩

/-- Campbell II.3.1: a kernel with no partial complement modulo the two-core
has precisely the two-core as its Sylow intersection. The normalizer used in
the Frattini argument contains Q, so the source condition is applied in G/Q. -/
theorem Embedding.sylow_inf_eq_core (d : Embedding T G) (K : Subgroup G) [K.Normal]
    (hQK : pCore 2 G ≤ K)
    (hK : NoPartialComplement (K.map (QuotientGroup.mk' (pCore 2 G)))) :
    (d.sylow : Subgroup G) ⊓ K = pCore 2 G := by
  let Q := pCore 2 G
  let P := (d.sylow : Subgroup G) ⊓ K
  let U := normalizer (P : Set G)
  let q := QuotientGroup.mk' Q
  have hQP : Q ≤ P := le_inf (pCore_isPGroup.le_sylow_of_normal d.sylow) hQK
  have hQU : Q ≤ U := hQP.trans P.le_normalizer
  obtain ⟨R, hR⟩ := d.sylow.exists_subgroupOf_eq_of_normal K
  have hRmap : (R : Subgroup K).map K.subtype = P := by
    rw [hR, subgroupOf_map_subtype]
  have hUK : U ⊔ K = ⊤ := by
    simpa only [hRmap] using R.normalizer_sup_eq_top
  have hm : K.map q ⊔ U.map q = ⊤ := by
    rw [← Subgroup.map_sup, sup_comm, hUK, map_top_of_surjective q
      (QuotientGroup.mk'_surjective Q)]
  have hUm : U.map q = ⊤ := hK _ hm
  have hUt : U = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hUm
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_eq_left.mpr hQU, comap_top] using hh
  have hPN : P.Normal := normalizer_eq_top_iff.mp hUt
  have hPP : IsPGroup 2 P := d.sylow.isPGroup'.to_le inf_le_left
  exact le_antisymm (le_sSup ⟨hPN, hPP⟩) hQP

/-- The actual natural section asserted by Campbell II.3.2. The actor map
realizes a rank-one quotient, and the equivariant projection identifies the
literal W/C_W(G) with F². This is a conclusion to construct, not an additional
hypothesis on `Embedding`; its existence is not proved in this module. -/
structure NaturalSection (d : Embedding T G) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  [charTwo : CharP F 2]
  actor : G →* SpecialLinearGroup (Fin 2) F
  actor_surjective : Function.Surjective actor
  core_le_kernel : pCore 2 G ≤ actor.ker
  noPartialComplement : NoPartialComplement (actor.ker.map (QuotientGroup.mk' (pCore 2 G)))
  kernel_centralizes : actor.ker ≤ centralizer (d.centerClosure : Set G)
  projection : d.centerClosure →* Multiplicative (Fin 2 → F)
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.ker = (Subgroup.center G).subgroupOf d.centerClosure
  equivariant : ∀ (g : G) (w : d.centerClosure),
    (projection (MulAut.conjNormal g w)).toAdd = actor g • (projection w).toAdd

attribute [instance] NaturalSection.field NaturalSection.finite NaturalSection.charTwo


/-- The projection with its proved kernel gives the actual source quotient
isomorphism, not merely a group-family label. -/
noncomputable def NaturalSection.quotientEquiv (d : Embedding T G) (m : NaturalSection d) :
    d.centerClosure ⧸ (Subgroup.center G).subgroupOf d.centerClosure ≃*
      Multiplicative (Fin 2 → m.F) :=
  (QuotientGroup.quotientMulEquivOfEq m.projection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective m.projection m.projection_surjective)

end CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell

end
