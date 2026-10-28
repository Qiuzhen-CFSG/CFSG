module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.CoreFusion
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.FullCentralizer
public import BenderSuzuki.SE.StrongEmbeddingConjugacy

/-!
# Ambient generation from actual involution fusion

In K = C_G(z) joined with M, every involution is K-conjugate to z or t.
Both representatives have their full ambient centralizer in K. An ambient
transporter between involutions of K therefore lies in K: match their
representatives using the retained K-conjugators and then use the full
centralizer. If K were proper, this proves strong embedding with its
nonvacuity and every intersection condition. The strong-embedding involution
conjugacy theorem contradicts the established ambient nonfusion of z and t.
Thus K = G, exactly the unchanged SourceCycleBase.Input.generate clause.
Neither simplicity of K nor simplicity of G is assumed in this argument.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (6.5)(2), printed p.602.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

omit [Finite G] in
private lemma transporter_mem_of_same_representative (K : Subgroup G) (r x g k l : G)
    (hk : k ∈ K) (hl : l ∈ K) (hx : MulAut.conj k r = x)
    (hy : MulAut.conj l r = MulAut.conj g x) (hC : centralizer r ≤ K) : g ∈ K := by
  have he : MulAut.conj (l⁻¹*g*k) r = r := by
    calc
      MulAut.conj (l⁻¹*g*k) r = MulAut.conj l⁻¹ (MulAut.conj g (MulAut.conj k r)) := by
        simp only [MulAut.conj_apply,mul_inv_rev,inv_inv,mul_assoc]
      _ = r := by rw [hx,←hy]; simp [MulAut.conj_apply,mul_assoc]
  have hc : l⁻¹*g*k ∈ centralizer r :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hh := K.mul_mem (K.mul_mem hl (hC hc)) (K.inv_mem hk)
  simpa [mul_assoc] using hh

/-- Every ambient transporter between involutions in the original join lies
in that join. The two cases use the full centralizers of z and t. -/
theorem join_involution_transporter (a : LocalData h) (hi : MarkerIntersection a)
    (x : G) (hx : x ∈ centralizer z ⊔ a.P.M) (ho : orderOf x = 2)
    (g : G) (hy : MulAut.conj g x ∈ centralizer z ⊔ a.P.M) :
    g ∈ centralizer z ⊔ a.P.M := by
  let K := centralizer z ⊔ a.P.M
  have hyorder : orderOf (MulAut.conj g x) = 2 := ((MulAut.conj g).orderOf_eq x).trans ho
  have hCt : centralizer (second a) ≤ K := (second_centralizer_le a hi).trans le_sup_right
  have hc : IsConj x (MulAut.conj g x) := isConj_iff.mpr ⟨g,rfl⟩
  rcases join_involution_fusion a x hx ho with ⟨k,hk,hkx⟩ | ⟨k,hk,hkx⟩ <;>
    rcases join_involution_fusion a _ hy hyorder with ⟨l,hl,hly⟩ | ⟨l,hl,hly⟩
  · exact transporter_mem_of_same_representative K z x g k l hk hl hkx hly le_sup_left
  · exact (not_isConj_second a (((isConj_iff.mpr ⟨k,hkx⟩).trans hc).trans
      (isConj_iff.mpr ⟨l,hly⟩).symm)).elim
  · exact (not_isConj_second a (((isConj_iff.mpr ⟨k,hkx⟩).trans hc).trans
      (isConj_iff.mpr ⟨l,hly⟩).symm).symm).elim
  · exact transporter_mem_of_same_representative K (second a) x g k l hk hl hkx hly hCt

/-- Full ambient involution centralizers stay in the join, with no
simplicity hypothesis on that join. -/
theorem join_centralizer_le (a : LocalData h) (hi : MarkerIntersection a)
    (x : G) (hx : x ∈ centralizer z ⊔ a.P.M) (ho : orderOf x = 2) :
    centralizer x ≤ centralizer z ⊔ a.P.M := by
  intro g hg
  apply join_involution_transporter a hi x hx ho g
  have he : MulAut.conj g x = x :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)
  rwa [he]

/-- Actual conjugators in K control ambient fusion of its involutions. -/
theorem join_controls_involution_fusion (a : LocalData h) (hi : MarkerIntersection a)
    (x y : G) (hx : x ∈ centralizer z ⊔ a.P.M) (hy : y ∈ centralizer z ⊔ a.P.M)
    (ho : orderOf x = 2) (hc : IsConj x y) :
    ∃ k ∈ centralizer z ⊔ a.P.M, MulAut.conj k x = y := by
  obtain ⟨k,hk⟩ := isConj_iff.mp hc
  have he : MulAut.conj k x = y := hk
  exact ⟨k,join_involution_transporter a hi x hx ho k (he.symm ▸ hy),he⟩

/-- AS91 (6.5)(2), in precisely the form required by SourceCycleBase.Input.
If the original join were proper, the transporter theorem proves every
strong-embedding premise; its two distinct involution classes exclude that. -/
theorem generate (a : LocalData h) (hi : MarkerIntersection a) :
    centralizer z ⊔ a.P.M = ⊤ := by
  classical
  let K := centralizer z ⊔ a.P.M
  by_contra hproper
  have hzK : z ∈ K := mem_sup_right (a.P.E_le a.marker_mem_E)
  have hzInv : BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp h.involution).2,(orderOf_eq_prime_iff.mp h.involution).1⟩
  have htInv : BenderSuzuki.PFAppendixIII.IsInvolution (second a) :=
    ⟨second_ne_one a,(orderOf_eq_prime_iff.mp (second_order a)).1⟩
  have hstrong : BenderSuzuki.IsStronglyEmbedded K := by
    refine ⟨hproper,⟨z,hzK,hzInv⟩,?_⟩
    intro g hg x hx hxg hxi
    change x ∈ K.map (MulAut.conj g⁻¹).toMonoidHom at hxg
    obtain ⟨y,hy,he⟩ := hxg
    change MulAut.conj g⁻¹ y = x at he
    have hxo : orderOf x = 2 := orderOf_eq_prime hxi.sq_eq_one hxi.ne_one
    have hyo : orderOf y = 2 := by
      have hh := (MulAut.conj g⁻¹).orderOf_eq y
      change orderOf (MulAut.conj g⁻¹ y) = orderOf y at hh
      rw [he,hxo] at hh
      exact hh.symm
    have hh := join_involution_transporter a hi y hy hyo g⁻¹ (he.symm ▸ hx)
    exact hg (K.inv_mem_iff.mp hh)
  obtain ⟨g,hg⟩ := hstrong.involutions_conjugate hzInv htInv
  apply not_isConj_second a
  refine isConj_iff.mpr ⟨g⁻¹,?_⟩
  simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem,inv_inv] using hg

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
