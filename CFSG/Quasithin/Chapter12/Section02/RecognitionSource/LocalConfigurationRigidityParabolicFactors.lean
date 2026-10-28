module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityResidualFixed
public import Theory.GroupTheory.CubicAutomorphismLines
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.SylowNormalizedResidual
/-!
# Canonical parabolic factors for the cyclic local pair

Write J=N_L(U), K=C_J(P), and W=U∩V. The cyclic pair already provides
U=W⊕Wᵍ for its chosen g∈P. Since K normalizes W and centralizes g, it
normalizes Wᵍ. An element of UV centralizing P centralizes both W and Wᵍ,
hence U; the action-kernel and order identities then put it in C_U(P)=1.
Thus the invariant-complement and separation fields require no tensor model.

If P has order three and J normalizes I=PUV, the literal residual identity
O²(I)=PU and Frattini's argument give J=U N_J(P). Every automorphism of P
is identity or inversion, and the original inverter in V converts this to
J=UVK. Together these are all three fields of ParabolicFactorization.
The final applications construct the actual parabolic complement and apply
the existing Gaschütz consumer, preserving the original Sylow subgroup T.

Finally, normality of Y=O²(N_L(W)) in N_G(C_T(U)) supplies the pair
normality: [I,Y]≤U follows on the two conjugate generators, and the
residual--Sylow supplement covers J by YT. The earlier centralizer
elimination then gives the exact rigidityStep conclusion, conditional only
on that residual normality, |P|=3, and the dimension cutoff.

The dimension branches and their assembly remain with
qt-d-12213-local-rigidity, which must discharge these three inputs and
construct the remaining marked quotient/tensor identifications. No
completion of those branches or of the full source theorem is asserted here.

Source: Aschbacher--Smith, original 12.2.25 and the construction before
12.2.26, printed pp.805--806.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityParabolic
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

omit [Finite G] in
private theorem normalizes_conjugate (K W : Subgroup G) (g : G)
    (hKW : K ≤ normalizer (W : Set G)) (hgK : g ∈ centralizer (K : Set G)) :
    K ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  rw [← map_equiv_normalizer_eq W (MulAut.conj g)]
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hKW
  have he : K.map (MulAut.conj g).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) hgK)
  rwa [he] at hh

/-- The conjugate axis is a complement invariant under the actual fixed actor. -/
theorem invariant_complement (D : ChosenModule T L V)
    (C : CyclicLocalAnalysis T L V d H P U) :
    ∃ W : Subgroup G, W ≤ U ∧ (U ⊓ V) ⊔ W = U ∧ Disjoint (U ⊓ V) W ∧
      parabolicFixedActor L U P ≤ normalizer (W : Set G) := by
  let := C.elementary
  obtain ⟨g,hg,hg1,hI,hU⟩ := C.pair
  let W := (U ⊓ V : Subgroup G).map (MulAut.conj g).toMonoidHom
  have hWU : W ≤ U := le_sup_right.trans hU.symm.le
  have hn : W ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (hWU.trans ((le_centralizer U).trans (centralizer_le inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcardW : Nat.card W = Nat.card (U ⊓ V : Subgroup G) :=
    Nat.card_congr ((U ⊓ V : Subgroup G).equivMapOfInjective _
      (MulAut.conj g).injective).toEquiv.symm
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes (U ⊓ V) W hn
  rw [hcardW,hU.symm,C.hyperplane,C.dimension,← pow_add,←two_mul] at hcard
  have hinter : Nat.card ((U ⊓ V) ⊓ W : Subgroup G) = 1 := by
    exact Nat.eq_of_mul_eq_mul_right
      (pow_pos (by decide : 0 < (2 : ℕ)) (2 * (d - 1)))
      (by simpa only [one_mul] using hcard.symm)
  refine ⟨W,hWU,hU.symm,disjoint_iff.mpr (eq_bot_of_card_eq _ hinter),?_⟩
  apply normalizes_conjugate
  · exact (le_inf (inf_le_left.trans inf_le_right)
      ((inf_le_left.trans inf_le_left).trans D.normalizes)).trans inf_normalizer_le_normalizer_inf
  · exact le_centralizer_iff.mp (inf_le_right : parabolicFixedActor L U P ≤ centralizer (P : Set G)) hg

omit [Finite G] in
/-- The fixed subgroup of U on V is exactly the displayed hyperplane. -/
theorem chosen_centralizer_core (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) :
    V ⊓ centralizer (U : Set G) = U ⊓ V := by
  let := C.elementary
  let X := V ⊓ centralizer (U : Set G)
  have hWX : U ⊓ V ≤ X := le_inf inf_le_right (inf_le_left.trans (le_centralizer U))
  have hi := relIndex_mul_relIndex (U ⊓ V) X V hWX inf_le_left
  rw [RigidityResidual.hyperplane_index A C] at hi
  have hp : ((U ⊓ V).relIndex X * X.relIndex V).Prime := hi.symm ▸ Nat.prime_two
  rcases (Nat.prime_mul_iff.mp hp) with hh | hh
  · have hVX : V ≤ X := relIndex_eq_one.mp hh.2
    have hUV : U ≤ centralizer (V : Set G) := le_centralizer_iff.mp (hVX.trans inf_le_right)
    have he : U = U ⊓ V := (inf_eq_left.mpr hUV).symm.trans C.action_kernel
    have hc := C.dimension
    rw [he,C.hyperplane] at hc
    have hd : d-1 < 2*(d-1) := by have := A.dimension.1; omega
    have hlt := pow_lt_pow_right₀ (by decide : 1 < (2 : ℕ)) hd
    omega
  · exact le_antisymm (relIndex_eq_one.mp hh.2) hWX

omit [Finite G] in
/-- Inside UV, the full centralizer of U is U itself. -/
theorem product_centralizer_core (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊔ V) ⊓ centralizer (U : Set G) = U := by
  let := C.elementary
  apply le_antisymm ?_ (le_inf le_sup_left (le_centralizer U))
  intro x hx
  have hprod : x ∈ (U : Set G) * (V : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U V (D.le_sylow.trans C.sylow_normalizes_core)]
    exact hx.1
  obtain ⟨a,ha,b,hb,rfl⟩ := hprod
  have hbC : b ∈ centralizer (U : Set G) := by
    simpa only [inv_mul_cancel_left] using (centralizer (U : Set G)).mul_mem
      ((centralizer _).inv_mem (le_centralizer U ha)) hx.2
  exact U.mul_mem ha ((chosen_centralizer_core A C).le ⟨hb,hbC⟩).1

omit [Finite G] in
/-- Fixing P forces an element of UV to fix both generating axes of U. -/
theorem product_fixed_eq_bot (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊔ V) ⊓ centralizer (P : Set G) = ⊥ := by
  let := C.elementary
  let := D.elementary
  let W := U ⊓ V
  obtain ⟨g,hg,hg1,hI,hU⟩ := C.pair
  have hfix : U ⊔ V ≤ centralizer (W : Set G) := sup_le
    ((le_centralizer U).trans (centralizer_le inf_le_left))
    ((le_centralizer V).trans (centralizer_le inf_le_right))
  apply eq_bot_iff.mpr
  intro x hx
  have hxW : x ∈ centralizer (W : Set G) := hfix hx.1
  have hgx : MulAut.conj g x = x := mul_inv_eq_iff_eq_mul.mpr (hx.2 g hg)
  have hxW' : x ∈ centralizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
    rintro _ ⟨w,hw,rfl⟩
    have hh := congrArg (MulAut.conj g) (hxW w hw)
    change (MulAut.conj g) w * x = x * (MulAut.conj g) w
    simpa only [map_mul,hgx] using hh
  have hxU : x ∈ centralizer (U : Set G) := by
    rw [hU]
    exact le_centralizer_iff.mp (sup_le
      (le_centralizer_iff.mp (show zpowers x ≤ centralizer (W : Set G) from
        zpowers_le.mpr hxW))
      (le_centralizer_iff.mp (show zpowers x ≤ centralizer
        (W.map (MulAut.conj g).toMonoidHom : Set G) from zpowers_le.mpr hxW'))) (mem_zpowers x)
  have hxU' : x ∈ U := (product_centralizer_core D A C).le ⟨hx.1,hxU⟩
  exact mem_bot.mp (C.fixed ▸ (show x ∈ U ⊓ centralizer (P : Set G) from ⟨hxU',hx.2⟩))

omit [Finite G] in
/-- The canonical fixed actor is disjoint from UV. -/
theorem separate (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    Disjoint (U ⊔ V) (parabolicFixedActor L U P) := by
  exact (disjoint_iff.mpr (product_fixed_eq_bot D A C)).mono_right inf_le_right

private theorem frattini_factor (J U P : Subgroup G) (hUJ : U ≤ J)
    (hPU : P ≤ normalizer (U : Set G))
    (hJP : J ≤ normalizer ((U ⊔ P : Subgroup G) : Set G))
    {p : ℕ} [Fact p.Prime] (S : Sylow p (U ⊔ P : Subgroup G))
    (hS : (S : Subgroup (U ⊔ P : Subgroup G)).map (U ⊔ P : Subgroup G).subtype = P) :
    U ⊔ (J ⊓ normalizer (P : Set G)) = J := by
  let K := U ⊔ P
  let M := J ⊔ K
  let K' := K.subgroupOf M
  let : K'.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (sup_le hJP K.le_normalizer)
  let e : K ≃* K' := (subgroupOfEquivOfLe (show K ≤ M from le_sup_right)).symm
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : (S' : Subgroup K').map K'.subtype = P.subgroupOf M := by
    apply map_injective M.subtype_injective
    change (((S : Subgroup K).map e.toMonoidHom).map K'.subtype).map M.subtype = _
    rw [map_map, map_map,
      map_subgroupOf_eq_of_le (show P ≤ M from le_sup_right.trans le_sup_right)]
    exact hS
  have hfr := S'.normalizer_sup_eq_top
  rw [hmap,sup_comm] at hfr
  apply le_antisymm (sup_le hUJ inf_le_left)
  intro j hj
  have hjM : (⟨j,mem_sup_left hj⟩ : M) ∈ K' ⊔ normalizer (P.subgroupOf M : Set M) := by
    rw [hfr]; exact mem_top _
  obtain ⟨k,hk,n,hn,hkn⟩ := mem_sup_of_normal_left.mp hjM
  have hkprod : (k : G) ∈ (U : Set G) * (P : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U P hPU]
    exact hk
  obtain ⟨u,hu,p,hp,hup⟩ := hkprod
  change u*p=(k : G) at hup
  have hnP : (n : G) ∈ normalizer (P : Set G) := by
    rw [← subgroupOf_normalizer_eq (show P ≤ M from le_sup_right.trans le_sup_right)] at hn
    exact hn
  have he : u * (p * (n : G)) = j := by
    rw [← mul_assoc,hup]
    exact congrArg Subtype.val hkn
  have hpJ : p * (n : G) ∈ J := by
    have hh := J.mul_mem (J.inv_mem (hUJ hu)) hj
    rw [← he,inv_mul_cancel_left] at hh
    exact hh
  rw [← he]
  exact mul_mem_sup hu ⟨hpJ,(normalizer (P : Set G)).mul_mem (P.le_normalizer hp) hnP⟩

private theorem odd_sylow (C : CyclicLocalAnalysis T L V d H P U) :
    ∃ S : Sylow (Nat.card P) (U ⊔ P : Subgroup G),
      (S : Subgroup (U ⊔ P : Subgroup G)).map (U ⊔ P : Subgroup G).subtype = P := by
  let : Fact (Nat.card P).Prime := ⟨C.prime_order⟩
  have hp : IsPGroup (Nat.card P) P := IsPGroup.of_card (n := 1) (by simp)
  let := C.elementary
  have hcop : (Nat.card U).Coprime (Nat.card P) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup (p := 2) (G := U)).exists_card_eq
    rw [hn]
    exact C.odd_order.coprime_two_left.pow_left n
  have hd : Disjoint U P := disjoint_of_coprime_natCard hcop
  have hPU : P ≤ normalizer (U : Set G) :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  let K := U ⊔ P
  let P' := P.subgroupOf K
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint U P hPU hd
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) P K bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,hc,mul_comm (Nat.card U)] at hi
  have he : P'.index = Nat.card U := Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  have hPi : IsPGroup (Nat.card P) P' := hp.of_equiv (subgroupOfEquivOfLe le_sup_right).symm
  have hnot : ¬ Nat.card P ∣ P'.index := by
    rw [he]
    exact C.prime_order.coprime_iff_not_dvd.mp hcop.symm
  exact ⟨hPi.toSylow hnot,by rw [IsPGroup.toSylow_coe]; exact map_subgroupOf_eq_of_le le_sup_right⟩

/-- Frattini and the original inverter give the literal factorization of J. -/
theorem generate_of_cubic_and_residual_normalized (D : ChosenModule T L V)
    (C : CyclicLocalAnalysis T L V d H P U) (hp : Nat.card P = 3)
    (hUL : U ≤ L)
    (hn : L ⊓ normalizer (U : Set G) ≤ normalizer ((P ⊔ U : Subgroup G) : Set G)) :
    U ⊔ V ⊔ parabolicFixedActor L U P = L ⊓ normalizer (U : Set G) := by
  let J := L ⊓ normalizer (U : Set G)
  let K := parabolicFixedActor L U P
  have hUJ : U ≤ J := le_inf hUL U.le_normalizer
  have hVJ : V ≤ J := le_inf D.le_component (D.le_sylow.trans C.sylow_normalizes_core)
  let : Fact (Nat.card P).Prime := ⟨C.prime_order⟩
  obtain ⟨S,hS⟩ := odd_sylow C
  have hPU : P ≤ normalizer (U : Set G) :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  have hf := frattini_factor J U P hUJ hPU (by simpa only [sup_comm U P] using hn) S hS
  apply le_antisymm (sup_le (sup_le hUJ hVJ) inf_le_left)
  apply hf.ge.trans
  refine sup_le (le_sup_left.trans le_sup_left) ?_
  intro x hx
  rcases CubicAutomorphismLines.automorphism_eq_one_or_inv hp
    (P.normalizerMonoidHom ⟨x,hx.2⟩) with hc | hi
  · have hxC : x ∈ centralizer (P : Set G) := by
      intro p hpP
      have he := congrArg (fun a : MulAut P => (a ⟨p,hpP⟩ : G)) hc
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    exact mem_sup_right (show x ∈ K from ⟨hx.1,hxC⟩)
  · obtain ⟨v,hv,hvU,hvi⟩ := C.inverted
    have hvc : v*x ∈ centralizer (P : Set G) := by
      intro p hpP
      have hxi : x*p*x⁻¹=p⁻¹ := congrArg Subtype.val (hi ⟨p,hpP⟩)
      have he : (v*x)*p*(v*x)⁻¹=p := by
        calc
          _ = v*(x*p*x⁻¹)*v⁻¹ := by group
          _ = v*p⁻¹*v⁻¹ := by rw [hxi]
          _ = p := by rw [hvi _ (P.inv_mem hpP),inv_inv]
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hvxK : v*x ∈ K := ⟨J.mul_mem (hVJ hv) hx.1,hvc⟩
    have hh := (U ⊔ V ⊔ K).mul_mem
      (mem_sup_left (mem_sup_right (V.inv_mem hv))) (mem_sup_right hvxK)
    change x ∈ U ⊔ V ⊔ K
    simpa only [inv_mul_cancel_left] using hh

/-- The residual of the literal pair is PU, not a residual of the ambient group. -/
theorem pair_residual (D : ChosenModule T L V)
    (C : CyclicLocalAnalysis T L V d H P U) :
    (pResidual 2 (cyclicPairJoin P U V)).map (cyclicPairJoin P U V).subtype = P ⊔ U := by
  rw [← C.residual]
  apply embedded_pResidual_eq_of_le_of_residual_le
  · exact sup_le (sup_le (by rw [C.overgroup]; exact le_sup_left)
      (C.core_le_sylow.trans C.sylow_le_overgroup))
      (D.le_sylow.trans C.sylow_le_overgroup)
  · rw [C.residual]
    exact le_sup_left

/-- The invariant complement and separation are automatic; generation follows
from the cubic actor and relative normality of its pair in the parabolic. -/
theorem factorization_of_cubic_and_pair_normalized (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hp : Nat.card P = 3) (hUL : U ≤ L)
    (hn : L ⊓ normalizer (U : Set G) ≤ normalizer (cyclicPairJoin P U V : Set G)) :
    ParabolicFactorization L V U P := by
  have hr : L ⊓ normalizer (U : Set G) ≤ normalizer ((P ⊔ U : Subgroup G) : Set G) := by
    rw [← pair_residual D C]
    exact hn.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))
  exact ⟨generate_of_cubic_and_residual_normalized D C hp hUL hr,
    separate D A C, invariant_complement D C⟩

/-- Both dimension branches feed the existing complement consumer through
actual pair normality. The remaining central-factor and cubic conclusions
are still owned by qt-d-12213-local-rigidity. -/
theorem source_parabolic_of_cubic_pair_normalized
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hp : Nat.card P = 3)
    (hn : L ⊓ normalizer (U : Set G) ≤ normalizer (cyclicPairJoin P U V : Set G)) :
    ParabolicSplitting T L V U := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hs := higher_kernel_vanishing_consequences D B hzero
  exact parabolicSplitting_of_cyclic_factorization D C
    (higher_normalizer_eq_of_kernel_vanishing h D structural A C B hzero)
    (factorization_of_cubic_and_pair_normalized D A C hp (C.core_le_sylow.trans hs.1) hn)

/-- Application to the existing Gaschütz splitting theorem, with all parabolic
factor premises constructed here. The source branches retain only their
normalizer, dimension and cubic-actor obligations. -/
theorem source_split_of_cubic_pair_normalized
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V)
    (hzero : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hd : d = 3 ∨ d = 4) (hp : Nat.card P = 3)
    (hn : L ⊓ normalizer (U : Set G) ≤ normalizer (cyclicPairJoin P U V : Set G)) :
    SplitLinearConfiguration L V d := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hs := higher_kernel_vanishing_consequences D B hzero
  exact splitLinearConfiguration_of_cyclic_factorization D A C hd
    (higher_normalizer_eq_of_kernel_vanishing h D structural A C B hzero) hs.2.1
    (factorization_of_cubic_and_pair_normalized D A C hp (C.core_le_sylow.trans hs.1) hn)

omit [Finite G] in
/-- Normalization by P extends the index-two displacement bound from V
to its conjugate generator, retaining the actual pair and residual. -/
theorem residual_pair_commutator (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hn : P ≤ normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    ⁅cyclicPairJoin P U V,rigidityHyperplaneResidual L U V⁆ ≤ U := by
  let Y := rigidityHyperplaneResidual L U V
  let W := U ⊓ V
  have hYL : Y ≤ L := (map_subtype_le _).trans inf_le_left
  have hYW : Y ≤ normalizer (W : Set G) := (map_subtype_le _).trans inf_le_right
  have hVY : ⁅V,Y⁆ ≤ W := commutator_le_of_normalized_index_two V W Y
    inf_le_right (RigidityResidual.hyperplane_index A C) (hYL.trans D.normalizes) hYW
  obtain ⟨g,hg,hg1,hI,hU⟩ := C.pair
  have hPH : P ≤ H := by rw [C.overgroup]; exact le_sup_left
  have heY : Y.map (MulAut.conj g).toMonoidHom = Y := mem_normalizer_iff_map_conj_eq.mp (hn hg)
  have heU : U.map (MulAut.conj g).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp (C.overgroup_normalizes_core (hPH hg))
  have hVgY : ⁅V.map (MulAut.conj g).toMonoidHom,Y⁆ ≤ U := by
    have he := map_mono (f := (MulAut.conj g).toMonoidHom) (hVY.trans inf_le_left)
    rwa [map_commutator,heY,heU] at he
  have hIH : cyclicPairJoin P U V ≤ H := sup_le (sup_le hPH
    (C.core_le_sylow.trans C.sylow_le_overgroup)) (D.le_sylow.trans C.sylow_le_overgroup)
  rw [hI]
  apply commutator_sup_le_of_relative_normal (cyclicPairJoin P U V) _ _ Y U
    (hIH.trans C.overgroup_normalizes_core) le_sup_right
    (by rw [hI]; exact le_sup_right) (hVY.trans inf_le_left) hVgY

/-- The parabolic lies in YT, so residual normality supplies pair normality. -/
theorem parabolic_normalizes_pair_of_residual_normal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    L ⊓ normalizer (U : Set G) ≤ normalizer (cyclicPairJoin P U V : Set G) := by
  let Y := rigidityHyperplaneResidual L U V
  let F := L ⊓ normalizer ((U ⊓ V : Subgroup G) : Set G)
  have hPN : P ≤ normalizer (Y : Set G) :=
    (le_sup_left.trans le_sup_left : P ≤ cyclicPairJoin P U V).trans
      ((higher_pair_normalizes_sylow_centralizer D A C).trans hn)
  have hYI : Y ≤ normalizer (cyclicPairJoin P U V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((residual_pair_commutator D A C hPN).trans (le_sup_right.trans le_sup_left))
  have hTV := ((structural G T L h).2.2 V D).1
  have hTW : (T : Subgroup G) ≤ normalizer ((U ⊓ V : Subgroup G) : Set G) :=
    (le_inf C.sylow_normalizes_core hTV).trans inf_normalizer_le_normalizer_inf
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf D.sylow_normalizes_component (hTW.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hJF : L ⊓ normalizer (U : Set G) ≤ F :=
    le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans D.normalizes)).trans
      inf_normalizer_le_normalizer_inf)
  exact (hJF.trans (le_embedded_pResidual_sup_sylow_of_normalizes T F hTF)).trans
    (sup_le hYI (C.sylow_le_overgroup.trans C.pair_normal))

/-- The exact rigidityStep output, with parabolic factors constructed. The
residual normality, cubic order and dimension bound remain with this task;
this conditional application does not prove the two source branches. -/
theorem source_rigidity_of_residual_normal_and_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3 ∨ d = 4) (hp : Nat.card P = 3)
    (hn : normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ≤
      normalizer (rigidityHyperplaneResidual L U V : Set G)) :
    (d = 3 ∨ d = 4) ∧ normalizer (L : Set G) = L ∧ L.pCoreIn 2 = V ∧
      ParabolicSplitting T L V U := by
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hzero := higher_component_centralizer_eq_bot_of_residual_normal h D A C B hn
    (RigidityResidual.radical_fixed_eq_component_centralizer h D structural A C B)
  exact ⟨hd,higher_normalizer_eq_of_kernel_vanishing h D structural A C B hzero,
    RigidityResidual.component_core_of_centralizers D B,
    source_parabolic_of_cubic_pair_normalized h D structural A C hnone hzero hp
      (parabolic_normalizes_pair_of_residual_normal h D structural A C hn)⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityParabolic
