module
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage
/-!
# Lifting a conjugate span through a p-group kernel

If the conjugate span has the whole action image and the kernel lies in the
conjugating subgroup, the span is normal and has p-group quotient. A
p-perfect original group therefore equals this span. Surjectivity onto an
artificially enlarged target is not required.

Source application: Aschbacher–Smith 13.3.15(6), printed p.894.
-/
public section
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]
theorem conjugateSpanBy_eq_top_of_image (p:ℕ) (f:G→*D) (A P:Subgroup G)
    (hG:pResidual p G=⊤) (hk:IsPGroup p f.ker) (hkP:f.ker≤P)
    (him:(conjugateSpanBy A P).map f=f.range) :
    conjugateSpanBy A P=⊤ := by
  let S:=conjugateSpanBy A P
  have hs:S⊔f.ker=⊤ := by
    rw [←comap_map_eq,him]
    exact top_unique (fun x _=>⟨x,rfl⟩)
  have hn:S.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hs]
    exact sup_le S.le_normalizer (hkP.trans (le_normalizer_conjugateSpanBy A P))
  let := hn
  have hquot:=isPGroup_quotient_of_sup_eq_top S f.ker hk hs
  exact top_unique (hG ▸ (show pResidual p G≤S from sInf_le ⟨hn,hquot⟩))
end Subgroup
