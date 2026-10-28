module
public import Theory.SpecificGroups.PSL3Two.PairedInvolutionGeometry
public import Theory.GroupTheory.FiveClassInvolutionTransfer
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Ambient transfer for the marked paired binary linear model

An embedded paired model whose indicated order-256 subgroup is an ambient
Sylow subgroup cannot retain the three nonfusion relations of 2.4.34. All
local class covers and centralizer bounds are supplied by the concrete model;
only ambient conjugacy separation and the literal Sylow marking are inputs.

Source: Aschbacher--Smith, proof of Lemma 2.4.34, printed p.548.
-/
public section
namespace Matrix.PSL3Two.PairedInvolutionGeometry
open Subgroup Theory.GroupTheory Theory.GroupTheory.PairedInvolutiveExtension
variable {G : Type*} [Group G] [Finite G]

/-- The marked local model contradicts the source's three ambient nonfusion
relations when its prescribed subgroup is the actual ambient Sylow subgroup. -/
theorem ambient_transfer_false
    (T : Sylow 2 G) (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (α : MulAut SL) (hα : Function.Involutive α) (houter : ∀ g : SL, α ≠ MulAut.conj g)
    (D : Subgroup SL) (hD : ∀ a∈D, α a∈D) (hcardD : Nat.card D = 8)
    (t : SL) (ht : t∈D) (htord : orderOf t = 2) (htfix : α t=t)
    (f : Model α hα →* G) (e : PairedSubgroup α hα D hD ≃* T)
    (he : ∀ u : PairedSubgroup α hα D hD, f u.val = (e u : G))
    (hxa : ¬ IsConj (f (graph α hα)) (f (base α hα t t)))
    (hxb : ¬ IsConj (f (graph α hα)) (f (base α hα 1 t)))
    (hba : ¬ IsConj (f (base α hα 1 t)) (f (base α hα t t))) : False := by
  let P := PairedSubgroup α hα D hD
  let a : P := diagonalIn α hα D hD t ht
  let b : P := pureIn α hα D hD t ht
  let x : P := graphIn α hα D hD
  let s : P := swapIn α hα D hD
  let y : P := graphSwapIn α hα D hD
  have he' (u : P) : f (u : Model α hα) = (e u : G) := he u
  have hconj (u v : P) (h : IsConj (u : Model α hα) (v : Model α hα)) :
      IsConj (e u : G) (e v : G) := by
    simpa only [he'] using f.map_isConj h
  have horder (u : P) : orderOf (u : Model α hα) = orderOf (e u : G) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, e.orderOf_eq]
  have hxord : orderOf (x : Model α hα) = 2 := by
    apply orderOf_eq_prime
    · change (graph α hα)^2=1
      simp [graph,pow_two]
    · intro heq
      have hh := congrArg (fun u : Model α hα => u.right.1) heq
      exact on_ne hh
  have hbord : orderOf (b : Model α hα) = 2 := by
    apply orderOf_eq_prime
    · change (base α hα 1 t)^2=1
      have ht2 : t*t=1 := by simpa only [htord,pow_two] using pow_orderOf_eq_one t
      simp [base,pow_two,ht2]
    · intro heq
      have hh : t=1 := congrArg (fun u : Model α hα => u.left.2) heq
      have hh' := htord
      rw [hh,orderOf_one] at hh'
      omega
  have hxa' : ¬ IsConj (e x : G) (e a : G) := by
    simpa only [← he', x, a, graphIn, diagonalIn] using hxa
  have hxb' : ¬ IsConj (e x : G) (e b : G) := by
    simpa only [← he', x, b, graphIn, pureIn] using hxb
  have hba' : ¬ IsConj (e b : G) (e a : G) := by
    simpa only [← he', b, a, pureIn, diagonalIn] using hba
  let U := (firstBit α hα D hD).ker.map e.toMonoidHom
  let V := (differenceBit α hα D hD).ker.map e.toMonoidHom
  have hUi : U.index=2 := by
    dsimp only [U]
    rw [index_map_of_bijective e.bijective]
    exact index_firstBit_ker α hα D hD
  have hVi : V.index=2 := by
    dsimp only [V]
    rw [index_map_of_bijective e.bijective]
    exact index_differenceBit_ker α hα D hD
  apply T.five_class_involution_transfer_false hno U V hUi hVi
    (e a) (e b) (e x) (e s) (e y) ((horder x).symm ▸ hxord)
    ((horder b).symm ▸ hbord) hxa' hxb' hba'
  · intro u hu hord
    obtain ⟨v,hv,rfl⟩ := hu
    rcases first_kernel_cover α hα D hD t ht htord v hv
      ((horder v).trans hord) with h | h | h
    · exact Or.inl (hconj a v h)
    · exact Or.inr (Or.inl (hconj b v h))
    · exact Or.inr (Or.inr (hconj s v h))
  · intro u hu hord
    obtain ⟨v,hv,rfl⟩ := hu
    rcases equal_bits_cover α hα D hD t ht htord v hv
      ((horder v).trans hord) with h | h | h
    · exact Or.inl (hconj a v h)
    · exact Or.inr (Or.inl (hconj b v h))
    · exact Or.inr (Or.inr (hconj y v h))
  · intro u hord
    obtain ⟨v,rfl⟩ := e.surjective u
    rcases centralizer_class_bound α hα houter D hD t ht htord hcardD v
      ((horder v).trans hord) with h | h | h
    · exact Or.inl (hconj a v h)
    · exact Or.inr (Or.inl (hconj b v h))
    · right; right
      rw [← Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e v).toEquiv,
        ← Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e s).toEquiv]
      exact h
  · intro u hu hord
    obtain ⟨v,rfl⟩ := e.surjective u
    have hv : v ∈ centralizer ({s} : Set P) := by
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hu
    rcases swap_centralizer_cover α hα houter D hD t ht htord v hv
      ((horder v).trans hord) with h | h | h | h
    · exact Or.inl (hconj a v h)
    · exact Or.inr (Or.inl (hconj x v h))
    · exact Or.inr (Or.inr (Or.inl (hconj s v h)))
    · exact Or.inr (Or.inr (Or.inr (hconj y v h)))
  · exact (pure_commute_graph α hα D hD t ht htfix).map e.toMonoidHom

end Matrix.PSL3Two.PairedInvolutionGeometry
