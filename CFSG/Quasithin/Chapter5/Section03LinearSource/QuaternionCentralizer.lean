module
public import CFSG.Quasithin.Chapter5.Section03LinearSource.MarkedNormalClosure
public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.Quaternion
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.PGroupCore

/-!
# Self-centralization of the exceptional normal closure

In characteristic two, a normal subgroup self-centralizing inside a Sylow
subgroup is self-centralizing in the whole group. Indeed its centralizer
inherits characteristic two, and its two-core lies in the Sylow subgroup
and in the original normal subgroup, so that core is central.

Apply this to the quaternion core marked by the original Sylow embedding,
inside the literal involution centralizer. The native calculation of
C_T(Q) supplies the Sylow premise. Relative normality and both subgroup
inclusions remain explicit for the prepared source consumer to discharge.
Source: Aschbacher--Smith §5.3.7, printed p.661 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter5.Section03LinearSource
variable {G : Type*} [Group G] [Finite G]

/-- In characteristic two, a normal subgroup self-centralizing in the Sylow
subgroup is self-centralizing in the ambient group. -/
private theorem centralizer_le_of_sylow (T : Sylow 2 G) (Q : Subgroup G) [Q.Normal]
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hT : (T : Subgroup G) ⊓ centralizer (Q : Set G) ≤ Q) :
    centralizer (Q : Set G) ≤ Q := by
  let C := centralizer (Q : Set G)
  let : C.Normal := inferInstance
  let : (C.pCoreIn 2).Normal := inferInstanceAs (((pCore 2 C).map C.subtype).Normal)
  have hRT : C.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 C).le_sylow_of_normal T
  have hRQ : C.pCoreIn 2 ≤ Q := (le_inf hRT (pCoreIn_le 2 C)).trans hT
  have hself := normal_core_selfCentralizing hc C
  intro x hx
  have hxc : (⟨x,hx⟩ : C) ∈ centralizer (pCore 2 C : Set C) := by
    intro r hr
    apply Subtype.ext
    exact (hx r (hRQ (mem_map_of_mem C.subtype hr)))
  exact hRQ (mem_map_of_mem C.subtype (hself hxc))

/-- A marked quaternion subgroup normal in an involution centralizer is
self-centralizing there when that centralizer has characteristic two. -/
theorem marked_quaternion_centralizer_le
    (c : Section03ExceptionalSylowModel.MarkedCopy G) (T : Sylow 2 G)
    (hT : c.carrier=(T : Subgroup G)) (D : Subgroup G)
    (hTD : (T : Subgroup G) ≤ D)
    (hQD : c.Q ≤ D) (hn : D ≤ normalizer (c.Q : Set G))
    (hchar : centralizer (pCore 2 D : Set D) ≤ pCore 2 D) :
    D ⊓ centralizer (c.Q : Set G) ≤ c.Q := by
  let Q := c.Q.subgroupOf D
  let : Q.Normal := normal_subgroupOf_of_le_normalizer hn
  have hlocal : (T.subtype hTD : Subgroup D) ⊓ centralizer (Q : Set D) ≤ Q := by
    rintro x ⟨hx,hc⟩
    let a := c.equiv.symm ⟨x.val,hT.symm ▸ hx⟩
    have ha : c.embedding a=x.val := congrArg Subtype.val (c.equiv.apply_symm_apply _)
    have hca : a ∈ centralizer (Matrix.PSL3Four.SylowModel.Q : Set Matrix.PSL3Four.SylowModel.T) := by
      intro b hb
      have hbQ : c.embedding b ∈ c.Q := mem_map_of_mem _ hb
      have hh := congrArg Subtype.val (hc ⟨c.embedding b,hQD hbQ⟩ hbQ)
      apply c.embedding_injective
      simpa only [map_mul,ha,Subgroup.coe_mul] using hh
    change x.val ∈ c.Q
    exact ha ▸ mem_map_of_mem c.embedding (Matrix.PSL3Four.SylowModel.centralizer_Q_le_Q hca)
  have hfull := centralizer_le_of_sylow (T.subtype hTD) Q hchar hlocal
  rintro x ⟨hx,hc⟩
  exact hfull (show (⟨x,hx⟩ : D) ∈ centralizer (Q : Set D) from
    fun y hy => Subtype.ext (hc y hy))
end CFSG.Quasithin.Chapter5.Section03LinearSource
