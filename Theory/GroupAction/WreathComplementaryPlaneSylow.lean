module
public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupAction.RegularWreathFunctionModule
public import Theory.Representation.FourGroupMatrixCoordinates
public import Theory.GroupAction.InvolutionDisplacementCard
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.Tactic

/-!
# A complementary plane and a generating Sylow in the natural wreath action

In the natural action of SL₂(2) wr C₂ on the elementary abelian group of
order sixteen, let I be a plane of order four invariant under a Sylow
two-subgroup S. For any involution t with displacement of order two, there
is one group element g that moves I to a complementary plane and makes
the conjugate Sylow S^g generate the whole wreath product together with t.
The public statement installs exactly the named matrix natural action and
regular-wreath function-module action.

For the standard dihedral Sylow, I must be the direct sum of its two fixed
coordinate lines. Indeed, a vector outside that plane has at least four
nonidentity points in its dihedral orbit, impossible in a subgroup of order
four. Involution rank-nullity turns the displacement hypothesis into fixed
order eight. An explicit constant-base matrix then moves both coordinate
lines away from themselves and from the active transvection's fixed line.
Kernel-checked finite identities show disjointness and express each of the
72 group elements using the conjugated dihedral subgroup and two products
with t. These explicit expressions prove the generation assertion.

Sylow conjugacy transports the plane and t to the standard coordinates,
and transports the same chosen mover back. The disjointness and generation
therefore use one common conjugating element. This finite-action lemma is
the selection step behind Stellmacher (9.10)(**), Journal of Algebra 190
(1997), printed p.58; the actual graph and quotient transport are separate
consumers. Every finite certificate is reduced by Lean's kernel.
-/

namespace RegularWreathProduct
private abbrev D := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev Q := Multiplicative (ZMod 2)
private abbrev F := Multiplicative (Fin 2 → ZMod 2)
private abbrev G := RegularWreathProduct D Q
private abbrev V := Q → F
private instance : MulDistribMulAction D F := FourGroupMatrixCoordinates.naturalAction
private instance : MulDistribMulAction G V := functionModule D Q F
private instance : DecidableEq G := fun a b => decidable_of_iff
  (a.left = b.left ∧ a.right = b.right) RegularWreathProduct.ext_iff.symm
private instance : Fintype G := Fintype.ofEquiv ((Q → D) × Q)
  (RegularWreathProduct.equivProd D Q).symm

private def K : Subgroup V where
  carrier v := ∀ i, (v i).toAdd 1 = 0
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro a b ha hb i
    change (a i).toAdd 1 + (b i).toAdd 1 = 0
    rw [ha,hb,add_zero]
  inv_mem' := by
    intro a ha i
    change -(a i).toAdd 1 = 0
    rw [ha,neg_zero]

private instance : DecidablePred (· ∈ K) := fun v =>
  inferInstanceAs (Decidable (∀ i, (v i).toAdd 1 = 0))

private def orbitList (v : V) : Finset V :=
  Finset.univ.image (fun d : DihedralGroup 4 => wreathTwoDihedralHom d • v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem outside_orbit_card : ∀ v : V, v ∉ K → 4 ≤ (orbitList v).card := by
  decide +kernel

private theorem K_card : Nat.card K = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem V_card : Nat.card V = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def selector (t : G) : G :=
  let lower : D := ⟨!![1, 0; 1, 1], by decide⟩
  let swap : D := ⟨!![0, 1; 1, 0], by decide⟩
  let active : Q := if t.left 1 = 1 then Multiplicative.ofAdd 1 else 1
  ⟨fun _ => if t.left active = lower then lower else swap, 1⟩

private def moved (t : G) (d : DihedralGroup 4) : G :=
  selector t * wreathTwoDihedralHom d * (selector t)⁻¹

private def cycle (t : G) : G :=
  moved t (if t.left 1 = 1 then .sr 1 else .sr 3) * t

private def otherCycle (t : G) : G :=
  moved t (.sr 0) * cycle t * (moved t (.sr 0))⁻¹

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
private theorem selector_spec : ∀ t : G, t ^ 2 = 1 →
    (Finset.univ.filter (fun v : V => t • v = v)).card = 8 →
    (∀ v : V, v ∈ K → selector t • v ∈ K → v = 1) ∧
    (∀ x : G, ∃ d : DihedralGroup 4, ∃ i j : Fin 3,
      x = moved t d * cycle t ^ i.val * otherCycle t ^ j.val) := by
  decide +kernel

private theorem invariant_plane_eq (I : Subgroup V) (hI : Nat.card I = 4)
    (hinv : ∀ d : DihedralGroup 4, ∀ v ∈ I, wreathTwoDihedralHom d • v ∈ I) :
    I = K := by
  classical
  apply Subgroup.eq_of_le_of_card_ge ?_ (by rw [hI,K_card])
  intro v hv
  by_contra hvK
  have horbit := outside_orbit_card v hvK
  have hone : (1 : V) ∉ orbitList v := by
    intro hmem
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hmem
    have hvone : v = 1 := (MulDistribMulAction.toMulAut G V (wreathTwoDihedralHom d)).map_eq_one_iff.mp hd
    exact hvK (hvone ▸ K.one_mem)
  have hsub : insert (1 : V) (orbitList v) ⊆ (I : Set V).toFinset := by
    intro w hw
    rw [Set.mem_toFinset]
    rcases Finset.mem_insert.mp hw with rfl | hmem
    · exact I.one_mem
    · obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hmem
      exact hinv d v hv
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hone,Set.toFinset_card,
    ← Nat.card_eq_fintype_card] at hcard
  change (orbitList v).card + 1 ≤ Nat.card I at hcard
  rw [hI] at hcard
  omega

private theorem standard_generates (t : G) (ht : t ^ 2 = 1)
    (hfixed : (Finset.univ.filter (fun v : V => t • v = v)).card = 8) :
    (wreathTwoSylow : Subgroup G).conjBy (selector t) ⊔ Subgroup.zpowers t = ⊤ := by
  let J := (wreathTwoSylow : Subgroup G).conjBy (selector t) ⊔ Subgroup.zpowers t
  have hm (d : DihedralGroup 4) : moved t d ∈ J := by
    apply (show (wreathTwoSylow : Subgroup G).conjBy (selector t) ≤ J from le_sup_left)
    apply Subgroup.mem_map.mpr
    exact ⟨wreathTwoDihedralHom d, wreathTwoSylow_coe ▸ ⟨d,rfl⟩, rfl⟩
  have htJ : t ∈ J := (show Subgroup.zpowers t ≤ J from le_sup_right) (Subgroup.mem_zpowers t)
  have hcycle : cycle t ∈ J := J.mul_mem (hm _) htJ
  have hother : otherCycle t ∈ J := J.mul_mem (J.mul_mem (hm _) hcycle) (J.inv_mem (hm _))
  apply top_unique
  intro x _
  obtain ⟨d,i,j,rfl⟩ := (selector_spec t ht hfixed).2 x
  exact J.mul_mem (J.mul_mem (hm d) (J.pow_mem hcycle _)) (J.pow_mem hother _)

private instance : IsElementaryAbelian 2 V where
  is_comm := ⟨fun a b => by funext i; exact mul_comm _ _⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro v
    funext i
    change (2 : ℕ) • (v i).toAdd = 0
    funext j
    change 2 • (v i).toAdd j = 0
    exact ZModModule.char_nsmul_eq_zero 2 _)

private theorem fixed_count (t : G) (ht : t ^ 2 = 1)
    (hdisp : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 2) :
    (Finset.univ.filter (fun v : V => t • v = v)).card = 8 := by
  have htne : t ≠ 1 := by
    intro htone
    have hbot : commutatorAction (Subgroup.zpowers t) V = ⊥ := by
      apply bot_unique
      rw [commutatorAction_eq_closure,Subgroup.closure_le]
      rintro _ ⟨b,v,rfl⟩
      have hb : (b : G) = 1 := by simpa [htone] using b.property
      change v⁻¹ * ((b:G) • v) = 1
      rw [hb,one_smul,inv_mul_cancel]
    rw [hbot,Subgroup.card_bot] at hdisp
    omega
  let gen : Subgroup.zpowers t := ⟨t,Subgroup.mem_zpowers t⟩
  have hgen : gen ≠ 1 ∧ gen ^ 2 = 1 :=
    ⟨fun h => htne (congrArg Subtype.val h),Subtype.ext ht⟩
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [V_card]; decide)
  have hcount := (card_two_action_fixed_commutator_card_data (U := V) gen hgen
    (by rw [Nat.card_zpowers,orderOf_eq_prime ht htne])).1
  rw [V_card,hdisp] at hcount
  have hcard : Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V) = 8 := by omega
  let e : (FixedPoints.subgroup (Subgroup.zpowers t) V) ≃ {v : V // t • v = v} := {
    toFun v := ⟨v,v.property gen⟩
    invFun v := ⟨v,fun b => smul_eq_self_of_mem_zpowers b.property v.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype] at hcard
  exact hcard

private theorem fixed_count_conjugate (u t : G) :
    (Finset.univ.filter (fun v : V => (u⁻¹*t*u) • v = v)).card =
      (Finset.univ.filter (fun v : V => t • v = v)).card := by
  let e : {v : V // (u⁻¹*t*u) • v = v} ≃ {v : V // t • v = v} := {
    toFun v := ⟨u • v,by
      have h := v.property
      simpa only [mul_smul,inv_smul_eq_iff] using h⟩
    invFun v := ⟨u⁻¹ • v,by
      simp only [mul_smul,smul_inv_smul,v.property]⟩
    left_inv _ := by apply Subtype.ext; exact inv_smul_smul _ _
    right_inv _ := by apply Subtype.ext; exact smul_inv_smul _ _ }
  have hh := Fintype.card_congr e
  simpa only [Fintype.card_subtype] using hh

set_option maxHeartbeats 1600000 in
public theorem exists_complementary_plane_generating_sylow :
    let D := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
    let Q := Multiplicative (ZMod 2)
    let F := Multiplicative (Fin 2 → ZMod 2)
    let G := RegularWreathProduct D Q
    let V := Q → F
    letI := FourGroupMatrixCoordinates.naturalAction
    letI := RegularWreathProduct.functionModule D Q F
    ∀ (S : Sylow 2 G) (t : G), t ^ 2 = 1 →
      Nat.card (commutatorAction (Subgroup.zpowers t) V) = 2 →
      ∀ I : Subgroup V, Nat.card I = 4 →
        (∀ s : S, ∀ v ∈ I, (s:G) • v ∈ I) →
        ∃ g : G, Disjoint I (I.map (MulDistribMulAction.toMulAut G V g).toMonoidHom) ∧
          (S : Subgroup G).conjBy g ⊔ Subgroup.zpowers t = ⊤ := by
  dsimp only
  intro S t ht hdisp I hI hinv
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq G wreathTwoSylow S
  have hS : (wreathTwoSylow : Subgroup G).conjBy u = (S : Subgroup G) := by
    exact congrArg (fun T : Sylow 2 G => (T : Subgroup G)) hu
  let f := MulDistribMulAction.toMulAut G V u⁻¹
  let I' := I.map f.toMonoidHom
  have hI'card : Nat.card I' = 4 := by
    change Nat.card (I.map f.toMonoidHom) = 4
    exact (Subgroup.card_map_of_injective (f := f.toMonoidHom) (K := I) f.injective).trans hI
  have hI'inv : ∀ d : DihedralGroup 4, ∀ v ∈ I', wreathTwoDihedralHom d • v ∈ I' := by
    intro d w hw
    obtain ⟨v,hv,rfl⟩ := hw
    have hs : u * wreathTwoDihedralHom d * u⁻¹ ∈ (S : Subgroup G) := by
      rw [←hS]
      exact ⟨wreathTwoDihedralHom d,wreathTwoSylow_coe ▸ ⟨d,rfl⟩,rfl⟩
    refine ⟨(u * wreathTwoDihedralHom d * u⁻¹) • v, hinv ⟨_,hs⟩ v hv, ?_⟩
    change u⁻¹ • ((u * wreathTwoDihedralHom d * u⁻¹) • v) =
      wreathTwoDihedralHom d • (u⁻¹ • v)
    simp only [mul_smul,inv_smul_smul]
  have hI'eq : I' = K := invariant_plane_eq I' hI'card hI'inv
  have htransport (v : V) (hv : v ∈ I) : u⁻¹ • v ∈ K := by
    rw [←hI'eq]
    exact Subgroup.mem_map_of_mem f.toMonoidHom hv
  let t' := u⁻¹ * t * u
  have ht' : t' ^ 2 = 1 := by
    change (u⁻¹ * t * u) ^ 2 = 1
    calc
      (u⁻¹ * t * u) ^ 2 = u⁻¹ * t ^ 2 * u := by
        simpa only [inv_inv] using (conj_pow (a := u⁻¹) (b := t) (i := 2))
      _ = 1 := by rw [ht]; simp
  have hfixed' : (Finset.univ.filter (fun v : V => t' • v = v)).card = 8 :=
    (fixed_count_conjugate u t).trans (fixed_count t ht hdisp)
  let k := selector t'
  let g := u * k * u⁻¹
  refine ⟨g, ?_, ?_⟩
  · apply Subgroup.disjoint_def.mpr
    intro v hv hvmap
    obtain ⟨w,hw,heq⟩ := hvmap
    have hkspec : ∀ z : V, z ∈ K → k • z ∈ K → z = 1 :=
      (selector_spec t' ht' hfixed').1
    have heq' : k • (u⁻¹ • w) = u⁻¹ • v := by
      rw [←heq]
      change k • (u⁻¹ • w) = u⁻¹ • ((u*k*u⁻¹) • w)
      simp only [mul_smul,inv_smul_smul]
    have hkw : k • (u⁻¹ • w) ∈ K := by
      rw [heq']
      exact htransport v hv
    have hwone : u⁻¹ • w = 1 := hkspec (u⁻¹ • w) (htransport w hw) hkw
    have hw1 : w = 1 := by
      have hh := congrArg (fun z : V => u • z) hwone
      simpa only [smul_inv_smul,smul_one] using hh
    rw [←heq,hw1,map_one]
  · have hstd := standard_generates t' ht' hfixed'
    have hm := congrArg (fun H : Subgroup G => H.map (MulAut.conj u).toMonoidHom) hstd
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,
      Subgroup.map_top_of_surjective _ (MulAut.conj u).surjective] at hm
    have htp : (MulAut.conj u).toMonoidHom t' = t := by
      change u * (u⁻¹ * t * u) * u⁻¹ = t
      group
    rw [htp] at hm
    change ((wreathTwoSylow : Subgroup G).conjBy k).conjBy u ⊔ Subgroup.zpowers t = ⊤ at hm
    have hconj : ((wreathTwoSylow : Subgroup G).conjBy k).conjBy u =
        (S : Subgroup G).conjBy g := by
      rw [←hS]
      simp only [Subgroup.conjBy_conjBy]
      congr 1
      simp only [g,mul_assoc,inv_mul_cancel,mul_one]
    rwa [hconj] at hm

end RegularWreathProduct
