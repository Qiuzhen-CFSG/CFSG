module
public import Theory.SpecificGroups.AlternatingSix.NonabelianInvolutionGeneration
public import Theory.SpecificGroups.PSL2.SevenInvolutionGeneration
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Centralizer generation from two four-groups in A₆ and PSL₃(2)

Two noncommuting elementary four-groups in a common Sylow two-subgroup
contain all its involutions. The Sylow subgroup is dihedral of order eight:
choose noncommuting involutions from the two four-groups, identify each
four-group with the corresponding centralizer in the Sylow subgroup, and
check that every involution commutes with at least one of the chosen pair.
The existing faithful dihedral-action generation theorems for the actual
A₆ and PSL₂(7) carriers then give generation by their element centralizers.

The public theorem retains the two given four-groups, the common Sylow
subgroup, and their literal centralizers. It supplies the local generation
step in Aschbacher–Smith, combined manuscript (1 March 2004), Lemma 2.4.34.
The model generation inputs are the involution fixed-group calculations of
Lemma 2.5.21, printed p.566. No centralizer-containment or source-balance
premise is assumed beyond the explicit containment in the receiving subgroup.
-/

public section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.PairedFourCentralizerGeneration

private theorem dihedral_centralizer_card (a b : DihedralGroup 4)
    (ha : a ^ 2 = 1) (hab : a * b ≠ b * a) :
    Nat.card (centralizer ({a} : Set (DihedralGroup 4))) = 4 := by
  let e : centralizer ({a} : Set (DihedralGroup 4)) ≃
      {x : DihedralGroup 4 // x * a = a * x} :=
    { toFun := fun x => ⟨x,mem_centralizer_singleton_iff.mp x.property⟩
      invFun := fun x => ⟨x,mem_centralizer_singleton_iff.mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  have h : ∀ a b : DihedralGroup 4, a ^ 2 = 1 → a * b ≠ b * a →
      Fintype.card {x : DihedralGroup 4 // x * a = a * x} = 4 := by decide +kernel
  exact h a b ha hab

private theorem dihedral_involution_commutes (a b x : DihedralGroup 4)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b ≠ b * a) (hx : x ^ 2 = 1) :
    x * a = a * x ∨ x * b = b * x := by
  have h : ∀ a b x : DihedralGroup 4, a ^ 2 = 1 → b ^ 2 = 1 → a * b ≠ b * a →
      x ^ 2 = 1 → x * a = a * x ∨ x * b = b * x := by decide +kernel
  exact h a b x ha hb hab hx

variable {D : Type*} [Group D] [Finite D]

private theorem paired_four_involution_cover (e : D ≃* DihedralGroup 4)
    (U V : Subgroup D) [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V]
    (hcU : Nat.card U = 4) (hcV : Nat.card V = 4)
    (a b : D) (ha : a ∈ U) (hb : b ∈ V) (hab : a * b ≠ b * a)
    (x : D) (hx : x ^ 2 = 1) : x ∈ U ∨ x ∈ V := by
  have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hb2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hea : (e a) ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have heb : (e b) ^ 2 = 1 := by rw [← map_pow, hb2, map_one]
  have heab : e a * e b ≠ e b * e a := by simpa only [← map_mul, e.injective.ne_iff] using hab
  have hCa : U = centralizer ({a} : Set D) := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro u hu
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) ⟨a,ha⟩)
    · rw [Nat.card_congr (GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e a).toEquiv,
        dihedral_centralizer_card (e a) (e b) hea heab, hcU]
  have hCb : V = centralizer ({b} : Set D) := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro u hu
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : V) ⟨b,hb⟩)
    · rw [Nat.card_congr (GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e b).toEquiv,
        dihedral_centralizer_card (e b) (e a) heb (Ne.symm heab), hcV]
  have he := dihedral_involution_commutes (e a) (e b) (e x) hea heb heab
    (by rw [← map_pow,hx,map_one])
  simpa only [hCa,hCb,mem_centralizer_singleton_iff,← map_mul,e.injective.eq_iff] using he

variable {K : Type*} [Group K] [Finite K]

private theorem model_sylow_dihedral
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (P : Sylow 2 K) : Nonempty (P ≃* DihedralGroup 4) := by
  rcases hmodel with he | he
  · obtain ⟨e⟩ := he
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    obtain ⟨q⟩ := AlternatingSix.ShadowLocal.alternatingSylow_dihedral Q
    exact ⟨((P : Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).trans q⟩
  · obtain ⟨e⟩ := he
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    obtain ⟨q⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral Q
    exact ⟨((P : Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).trans q⟩

omit [Finite K] in
private theorem fixed_le_map {M : Type*} [Group M] (e : K ≃* M)
    (P N : Subgroup K)
    (hfix : ∀ i : P, orderOf i = 2 → centralizer ({(i : K)} : Set K) ≤ N)
    (i : P) (hi : orderOf i = 2) :
    (MulAut.conj (e i)).fixedSubgroup ≤ N.map e.toMonoidHom := by
  rw [MulAut.fixedSubgroup_conj,
    ← GroupTheory.CentralizerSmallKernelTransport.map_centralizer e (i : K)]
  exact Subgroup.map_mono (hfix i hi)

omit [Finite K] in
private theorem eq_top_of_map_eq_top {M : Type*} [Group M] (e : K ≃* M)
    (N : Subgroup K) (hN : N.map e.toMonoidHom = ⊤) : N = ⊤ := by
  apply top_unique
  intro x _
  have he : e x ∈ N.map e.toMonoidHom := hN ▸ mem_top (e x)
  obtain ⟨y,hy,he⟩ := he
  exact e.injective he ▸ hy

private theorem model_centralizer_generation
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (P : Sylow 2 K) (N : Subgroup K)
    (hfix : ∀ i : P, orderOf i = 2 → centralizer ({(i : K)} : Set K) ≤ N) : N = ⊤ := by
  obtain ⟨eP⟩ := model_sylow_dihedral hmodel P
  rcases hmodel with he | he
  · obtain ⟨e⟩ := he
    let f : P →* MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.conj : alternatingGroup (Fin 6) →* _).comp
        (e.toMonoidHom.comp (P : Subgroup K).subtype)
    have hf : Function.Injective f := AlternatingSix.ShadowLocal.inner_injective.comp
      (e.injective.comp Subtype.val_injective)
    obtain ⟨a,b,ha,hb,hab⟩ := DihedralGroup.exists_noncommuting_involutions
      (k := 2) (by decide) eP
    apply eq_top_of_map_eq_top e N
    exact AlternatingSix.NonabelianInvolutionGeneration.fixed_generation_of_noncommuting_involutions
      P.isPGroup' f hf a b (by simpa only [ha] using pow_orderOf_eq_one a)
      (by simpa only [hb] using pow_orderOf_eq_one b) hab
      (N.map e.toMonoidHom) (fixed_le_map e P N hfix)
  · obtain ⟨e₀⟩ := he
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    let e : K ≃* PSL(2,ZMod 7) :=
      e₀.trans Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm
    let f : P →* MulAut PSL(2,ZMod 7) :=
      (MulAut.conj : PSL(2,ZMod 7) →* _).comp
        (e.toMonoidHom.comp (P : Subgroup K).subtype)
    have hf : Function.Injective f :=
      (MulAut.conj_injective_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot (ZMod 7))).comp
        (e.injective.comp Subtype.val_injective)
    apply eq_top_of_map_eq_top e N
    exact Theory.PSL2.SevenInvolutionGeneration.fixed_generation_of_dihedral (k := 2)
      (by decide) eP f hf (N.map e.toMonoidHom) (fixed_le_map e P N hfix)

/-- The centralizers of the nonidentity elements of two noncommuting four-groups
in a common Sylow two-subgroup generate the actual A₆ or PSL₃(2) model. -/
theorem eq_top_of_paired_four
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (P : Sylow 2 K) (U V N : Subgroup K)
    (hU : IsElementaryAbelian 2 U) (hV : IsElementaryAbelian 2 V)
    (hcU : Nat.card U = 4) (hcV : Nat.card V = 4)
    (hUP : U ≤ (P : Subgroup K)) (hVP : V ≤ (P : Subgroup K))
    (hnc : ¬ V ≤ centralizer (U : Set K))
    (hC : ∀ x : K, (x ∈ U ∨ x ∈ V) → x ≠ 1 → centralizer ({x} : Set K) ≤ N) :
    N = ⊤ := by
  let := hU
  let := hV
  obtain ⟨eP⟩ := model_sylow_dihedral hmodel P
  have hex : ∃ a ∈ U, ∃ b ∈ V, a * b ≠ b * a := by
    by_contra hn
    push Not at hn
    exact hnc (fun b hb a ha => hn a ha b hb)
  obtain ⟨a,ha,b,hb,hab⟩ := hex
  let aP : P := ⟨a,hUP ha⟩
  let bP : P := ⟨b,hVP hb⟩
  let : IsElementaryAbelian 2 (U.subgroupOf P) := IsElementaryAbelian.subgroupOf hUP
  let : IsElementaryAbelian 2 (V.subgroupOf P) := IsElementaryAbelian.subgroupOf hVP
  have hcardU : Nat.card (U.subgroupOf P) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv).trans hcU
  have hcardV : Nat.card (V.subgroupOf P) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv).trans hcV
  apply model_centralizer_generation hmodel P N
  intro i hi
  have hmem : (i : K) ∈ U ∨ (i : K) ∈ V :=
    paired_four_involution_cover eP (U.subgroupOf P) (V.subgroupOf P) hcardU hcardV
      aP bP ha hb (fun hh => hab (congrArg Subtype.val hh)) i (by simpa only [hi] using pow_orderOf_eq_one i)
  apply hC i hmem
  intro he
  have hie : i = 1 := Subtype.ext he
  simp [hie] at hi


end Theory.SpecificGroups.PairedFourCentralizerGeneration
