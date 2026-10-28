module
public import Theory.GroupTheory.PairedInvolutiveExtension
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Local involution fusion for two exchanged factors

A single involution class in each factor and trivial graph cocycles give five
classes in the paired extension. The two actor kernels have three-class
covers. Commuting with the swapping involution forces equal coordinates,
so its centralizer has a four-class cover excluding the pure-factor class.
All conjugators belong to the same extension and preserve the specified marks.

Source: Aschbacher--Smith, proof of 2.4.34, printed p.548 of the
1 March 2004 manuscript. These are the intrinsic covers used by the two
Thompson-transfer applications in that proof.
-/

public section
namespace Theory.GroupTheory.PairedInvolutiveExtension
variable {K : Type*} [Group K] (α : MulAut K) (hα : Function.Involutive α)

private theorem mk_eq_one_iff (a b : K) (p q : Bit) :
    mk α hα a b p q = 1 ↔ a = 1 ∧ b = 1 ∧ p = 1 ∧ q = 1 := by
  change SemidirectProduct.mk (a,b) (p,q) = SemidirectProduct.mk (1,1) (1,1) ↔ _
  simp [SemidirectProduct.ext_iff, Prod.ext_iff, and_assoc]

private theorem square_base (a b : K) (h : (mk α hα a b 1 1)^2 = 1) :
    a^2=1 ∧ b^2=1 := by
  rw [pow_two, mk_mul, action_one] at h
  have hh := (mk_eq_one_iff α hα _ _ _ _).mp h
  exact ⟨by simpa only [pow_two] using hh.1, by simpa only [pow_two] using hh.2.1⟩

private theorem square_swap (a b : K) (h : (mk α hα a b 1 on)^2 = 1) :
    b=a⁻¹ := by
  have hh := congrArg (fun u : Model α hα => u.left.1) h
  have hab : a*b=1 := by simpa [pow_two, mk_mul, mk] using hh
  exact (inv_eq_of_mul_eq_one_right hab).symm

private theorem square_graph (a b : K) (h : (mk α hα a b on 1)^2 = 1) :
    a*α a=1 ∧ b*α b=1 := by
  have hh := congrArg (fun u : Model α hα => u.left) h
  simpa [pow_two, mk_mul, mk, Prod.ext_iff] using hh

private theorem square_graphSwap (a b : K) (h : (mk α hα a b on on)^2 = 1) :
    b=α a⁻¹ := by
  have hh := congrArg (fun u : Model α hα => u.left.1) h
  have hab : a*α b=1 := by simpa [pow_two, mk_mul, mk] using hh
  have hi : α b=a⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  exact (hα b).symm.trans (congrArg α hi)

private theorem isConj_base (a b c d : K) (hac : IsConj a c) (hbd : IsConj b d) :
    IsConj (base α hα a b) (base α hα c d) := by
  obtain ⟨u, hu⟩ := isConj_iff.mp hac
  obtain ⟨v, hv⟩ := isConj_iff.mp hbd
  refine isConj_iff.mpr ⟨base α hα u v, ?_⟩
  rw [base_conj, hu, hv]

/-- The swap coset has one involution class, with an explicit base conjugator. -/
theorem isConj_swap (a b : K) (h : (mk α hα a b 1 on)^2=1) :
    IsConj (mk α hα a b 1 on) (swap α hα) := by
  rw [square_swap α hα a b h]
  exact isConj_iff.mpr ⟨base α hα a⁻¹ 1, conjugate_swap α hα a⟩

/-- The graph-swap coset also has one involution class. -/
theorem isConj_graphSwap (a b : K) (h : (mk α hα a b on on)^2=1) :
    IsConj (mk α hα a b on on) (graphSwap α hα) := by
  rw [square_graphSwap α hα a b h]
  exact isConj_iff.mpr ⟨base α hα a⁻¹ 1, conjugate_graphSwap α hα a⟩

/-- A vanishing graph cocycle normalizes both factors independently. -/
theorem isConj_graph
    (hcocycle : ∀ a : K, a * α a = 1 → ∃ b : K, b*a*(α b)⁻¹=1)
    (a b : K) (h : (mk α hα a b on 1)^2=1) :
    IsConj (mk α hα a b on 1) (graph α hα) := by
  obtain ⟨ha,hb⟩ := square_graph α hα a b h
  obtain ⟨c,hc⟩ := hcocycle a ha
  obtain ⟨d,hd⟩ := hcocycle b hb
  refine isConj_iff.mpr ⟨base α hα c d, ?_⟩
  rw [conjugate_graph, hc, hd]
  rfl

variable (t : K) (hclass : ∀ a : K, a^2=1 → a≠1 → IsConj a t)
include hclass

/-- Nontrivial base involutions are pure or supported on both factors. -/
theorem base_involution_fusion (a b : K)
    (h : (base α hα a b)^2=1) (hne : base α hα a b≠1) :
    IsConj (base α hα a b) (base α hα t t) ∨
      IsConj (base α hα a b) (base α hα 1 t) := by
  obtain ⟨ha,hb⟩ := square_base α hα a b h
  by_cases ha1 : a=1
  · have hb1 : b≠1 := by intro hb1; apply hne; simp [base,ha1,hb1]
    exact Or.inr (isConj_base α hα a b 1 t (by simpa only [ha1] using (IsConj.refl (1 : K))) (hclass b hb hb1))
  · by_cases hb1 : b=1
    · right
      have hs : IsConj (base α hα a b) (base α hα b a) :=
        isConj_iff.mpr ⟨swap α hα, swap_conj_base α hα a b⟩
      exact hs.trans (isConj_base α hα b a 1 t (by simpa only [hb1] using (IsConj.refl (1 : K))) (hclass a ha ha1))
    · exact Or.inl (isConj_base α hα a b t t (hclass a ha ha1) (hclass b hb hb1))

/-- Exact five-representative coverage inside this extension. -/
theorem involution_fusion
    (hcocycle : ∀ a : K, a * α a = 1 → ∃ b : K, b*a*(α b)⁻¹=1)
    (u : Model α hα) (hu : u^2=1) (hne : u≠1) :
    IsConj u (base α hα t t) ∨ IsConj u (base α hα 1 t) ∨
      IsConj u (graph α hα) ∨ IsConj u (swap α hα) ∨ IsConj u (graphSwap α hα) := by
  rcases u with ⟨⟨a,b⟩,⟨p,q⟩⟩
  rcases bit_cases p with rfl|rfl <;> rcases bit_cases q with rfl|rfl
  · exact (base_involution_fusion α hα t hclass a b hu hne).imp id Or.inl
  · exact Or.inr (Or.inr (Or.inr (Or.inl (isConj_swap α hα a b hu))))
  · exact Or.inr (Or.inr (Or.inl (isConj_graph α hα hcocycle a b hu)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (isConj_graphSwap α hα a b hu))))

/-- The actor-first-bit kernel has only the two base classes and the swap class. -/
theorem first_kernel_fusion (u : Model α hα) (hp : u.right.1=1)
    (hu : u^2=1) (hne : u≠1) :
    IsConj u (base α hα t t) ∨ IsConj u (base α hα 1 t) ∨ IsConj u (swap α hα) := by
  rcases u with ⟨⟨a,b⟩,⟨p,q⟩⟩
  change p=1 at hp
  subst p
  rcases bit_cases q with rfl|rfl
  · exact (base_involution_fusion α hα t hclass a b hu hne).imp id Or.inl
  · exact Or.inr (Or.inr (isConj_swap α hα a b hu))

/-- Equality of the two actor bits gives the analogous graph-swap cover. -/
theorem equal_bits_fusion (u : Model α hα) (hp : u.right.1=u.right.2)
    (hu : u^2=1) (hne : u≠1) :
    IsConj u (base α hα t t) ∨ IsConj u (base α hα 1 t) ∨ IsConj u (graphSwap α hα) := by
  rcases u with ⟨⟨a,b⟩,⟨p,q⟩⟩
  change p=q at hp
  subst p
  rcases bit_cases q with rfl|rfl
  · exact (base_involution_fusion α hα t hclass a b hu hne).imp id Or.inl
  · exact Or.inr (Or.inr (isConj_graphSwap α hα a b hu))

omit hclass in
/-- Commuting with the pure interchange forces equal base coordinates. -/
theorem commute_swap_iff (u : Model α hα) : Commute u (swap α hα) ↔ u.left.1=u.left.2 := by
  rcases u with ⟨⟨a,b⟩,⟨p,q⟩⟩
  rcases bit_cases p with rfl|rfl <;> rcases bit_cases q with rfl|rfl <;>
    change Commute (mk α hα a b _ _) (swap α hα) ↔ _
  all_goals
    change _ * _ = _ * _ ↔ _
    simp only [swap,mk_mul,action_one,action_graph,action_swap,action_graphSwap,
      map_one,mul_one,one_mul]
    simp [mk,SemidirectProduct.ext_iff,Prod.ext_iff,eq_comm]

/-- The interchange centralizer excludes the pure-factor involution class. -/
theorem swap_centralizer_fusion
    (hcocycle : ∀ a : K, a * α a = 1 → ∃ b : K, b*a*(α b)⁻¹=1)
    (u : Model α hα) (hc : Commute u (swap α hα)) (hu : u^2=1) (hne : u≠1) :
    IsConj u (base α hα t t) ∨ IsConj u (graph α hα) ∨
      IsConj u (swap α hα) ∨ IsConj u (graphSwap α hα) := by
  have he := (commute_swap_iff α hα u).mp hc
  rcases u with ⟨⟨a,b⟩,⟨p,q⟩⟩
  change a=b at he
  subst b
  rcases bit_cases p with rfl|rfl <;> rcases bit_cases q with rfl|rfl
  · have ha : a^2=1 := (square_base α hα a a hu).1
    have ha1 : a≠1 := by intro he; apply hne; subst a; rfl
    exact Or.inl (isConj_base α hα a a t t (hclass a ha ha1) (hclass a ha ha1))
  · exact Or.inr (Or.inr (Or.inl (isConj_swap α hα a a hu)))
  · exact Or.inr (Or.inl (isConj_graph α hα hcocycle a a hu))
  · exact Or.inr (Or.inr (Or.inr (isConj_graphSwap α hα a a hu)))

end Theory.GroupTheory.PairedInvolutiveExtension
