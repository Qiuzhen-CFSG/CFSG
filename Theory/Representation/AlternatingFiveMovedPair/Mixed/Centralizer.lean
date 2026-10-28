module
public import Theory.Representation.AlternatingFiveMovedPair.Mixed.ScalarCommutants

/-!
# Centralizer of the mixed alternating-five pair

For the binary natural module `N` of `SL₂(4)` and the deleted permutation
module `D`, the centralizer on `(N ⊗ D) × (D ⊗ N)` consists of independent
`GF(4)` scalars on the two summands. Tensor contractions reduce this to the
single-factor scalar commutants; the two mixed summands have no nonzero
intertwiners. Consequently a centralizing involution is the identity.

The marked pair action and its symmetric-five extension are faithful. These
facts support the mixed-module moved-space estimate in the quasithin argument
of Aschbacher–Smith, Appendix D, §3 (especially D.3.5).
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Mixed
open SL2FourNatural SL2FourNatural.SemilinearNormalizer
abbrev ndAction : Representation (ZMod 2) (SL × SL) ND :=
  Representation.tprod (ν.comp (MonoidHom.fst _ _)) (δ.comp (MonoidHom.snd _ _))
abbrev dnAction : Representation (ZMod 2) (SL × SL) DN :=
  Representation.tprod (δ.comp (MonoidHom.fst _ _)) (ν.comp (MonoidHom.snd _ _))

lemma action_special (g : SL × SL) (u : ND) (v : DN) :
    action g (u,v) = (ndAction g u, dnAction g v) := by
  have h1 : first (specialFiveLines g.1,specialFiveLines g.2) = ndAction g := by
    change _root_.TensorProduct.map (naturalAction (specialFiveLines g.1)) (δ g.2) = _
    rw [naturalAction_special]
    rfl
  have h2 : second (specialFiveLines g.1,specialFiveLines g.2) = dnAction g := by
    change _root_.TensorProduct.map (δ g.1) (naturalAction (specialFiveLines g.2)) = _
    rw [naturalAction_special]
    rfl
  exact Prod.ext (LinearMap.congr_fun h1 u) (LinearMap.congr_fun h2 v)

def scalarNatural (c : F) : Natural →ₗ[ZMod 2] Natural :=
  (LinearMap.lsmul F Natural c).restrictScalars (ZMod 2)
def scalarND (c : F) : ND →ₗ[ZMod 2] ND := _root_.TensorProduct.map (scalarNatural c) 1
def scalarDN (c : F) : DN →ₗ[ZMod 2] DN := _root_.TensorProduct.map 1 (scalarNatural c)

private def contractR {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] (l : W →ₗ[ZMod 2] ZMod 2) :
    U ⊗[ZMod 2] W →ₗ[ZMod 2] U :=
  (_root_.TensorProduct.rid (ZMod 2) U).toLinearMap.comp (l.lTensor U)
private def contractL {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] (l : U →ₗ[ZMod 2] ZMod 2) :
    U ⊗[ZMod 2] W →ₗ[ZMod 2] W :=
  (_root_.TensorProduct.lid (ZMod 2) W).toLinearMap.comp (l.rTensor W)

private lemma contractR_tmul {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] (l : W →ₗ[ZMod 2] ZMod 2) (u : U) (v : W) :
    contractR l (u ⊗ₜ[ZMod 2] v) = l v • u := by simp [contractR]
private lemma contractL_tmul {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] (l : U →ₗ[ZMod 2] ZMod 2) (u : U) (v : W) :
    contractL l (u ⊗ₜ[ZMod 2] v) = l u • v := by simp [contractL]
private lemma contract_comm {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W]
    (l : U →ₗ[ZMod 2] ZMod 2) (r : W →ₗ[ZMod 2] ZMod 2) (x : U ⊗[ZMod 2] W) :
    l (contractR r x) = r (contractL l x) := by
  induction x using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [contractR_tmul, contractL_tmul, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]
private lemma contractR_left {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] (l : W →ₗ[ZMod 2] ZMod 2)
    (a : Module.End (ZMod 2) U) (x : U ⊗[ZMod 2] W) :
    contractR l (_root_.TensorProduct.map a 1 x) = a (contractR l x) := by
  induction x using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [contractR_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
private lemma contractL_right {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] (l : U →ₗ[ZMod 2] ZMod 2)
    (a : Module.End (ZMod 2) W) (x : U ⊗[ZMod 2] W) :
    contractL l (_root_.TensorProduct.map 1 a x) = a (contractL l x) := by
  induction x using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [contractL_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
private lemma contractR_ext {U W : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {x y : U ⊗[ZMod 2] W}
    (h : ∀ l : W →ₗ[ZMod 2] ZMod 2, contractR l x = contractR l y) : x = y := by
  let b := Module.finBasis (ZMod 2) W
  apply (_root_.TensorProduct.equivFinsuppOfBasisRight b).injective
  apply Finsupp.ext
  intro i
  simpa only [_root_.TensorProduct.equivFinsuppOfBasisRight_apply, contractR,
    LinearMap.comp_apply, LinearEquiv.coe_coe] using h (b.coord i)

lemma dn_commuting_scalar (f : DN →ₗ[ZMod 2] DN)
    (hf : ∀ (g : SL × SL) v, f (dnAction g v) = dnAction g (f v)) :
    ∃ c : F, f = scalarDN c := by
  let : Nontrivial Deleted := Module.nontrivial_of_finrank_pos (by rw [finrank_deleted]; decide)
  obtain ⟨z,hz⟩ := exists_ne (0 : Deleted)
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz
  let t : Natural →ₗ[ZMod 2] Natural :=
    (contractL l).comp (f.comp (_root_.TensorProduct.mk (ZMod 2) Deleted Natural z))
  have hright (g : SL) (v : Natural) : t (ν g v) = ν g (t v) := by
    change contractL l (f (z ⊗ₜ[ZMod 2] ν g v)) = _
    have he : z ⊗ₜ[ZMod 2] ν g v = dnAction (1,g) (z ⊗ₜ[ZMod 2] v) := by
      change _ = δ 1 z ⊗ₜ[ZMod 2] ν g v
      simp
    rw [he,hf]
    change contractL l (_root_.TensorProduct.map (δ 1) (ν g) (f (z ⊗ₜ[ZMod 2] v))) = _
    rw [map_one]
    exact contractL_right l (ν g) _
  obtain ⟨c,hc⟩ := natural_commuting_scalar t hright
  refine ⟨c, ?_⟩
  have htensor (u : Deleted) (v : Natural) : f (u ⊗ₜ[ZMod 2] v) = u ⊗ₜ[ZMod 2] t v := by
    apply contractR_ext
    intro r
    let T : Deleted →ₗ[ZMod 2] Deleted :=
      (contractR r).comp (f.comp ((_root_.TensorProduct.mk (ZMod 2) Deleted Natural).flip v))
    have hT (g : SL) (u : Deleted) : T (δ g u) = δ g (T u) := by
      change contractR r (f (δ g u ⊗ₜ[ZMod 2] v)) = _
      have he : δ g u ⊗ₜ[ZMod 2] v = dnAction (g,1) (u ⊗ₜ[ZMod 2] v) := by
        change _ = δ g u ⊗ₜ[ZMod 2] ν 1 v
        simp
      rw [he,hf]
      change contractR r (_root_.TensorProduct.map (δ g) (ν 1) (f (u ⊗ₜ[ZMod 2] v))) = _
      rw [map_one]
      exact contractR_left r (δ g) _
    obtain ⟨a,ha⟩ := deleted_commuting_scalar T hT
    have hat : a = r (t v) := by
      have hh := congrArg l (ha z)
      change l (contractR r (f (z ⊗ₜ[ZMod 2] v))) = l (a • z) at hh
      rw [contract_comm,map_smul,hl,smul_eq_mul,mul_one] at hh
      exact hh.symm
    change T u = contractR r (u ⊗ₜ[ZMod 2] t v)
    rw [ha,contractR_tmul,hat]
  apply _root_.TensorProduct.ext'
  intro u v
  rw [htensor,hc]
  rfl

lemma nd_commuting_scalar (f : ND →ₗ[ZMod 2] ND)
    (hf : ∀ (g : SL × SL) v, f (ndAction g v) = ndAction g (f v)) :
    ∃ c : F, f = scalarND c := by
  let e := _root_.TensorProduct.comm (ZMod 2) Deleted Natural
  let t := e.symm.toLinearMap.comp (f.comp e.toLinearMap)
  have he (g : SL × SL) (x : DN) : e (dnAction g x) = ndAction (g.2,g.1) (e x) := by
    induction x using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul u v => rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  have ht (g : SL × SL) (x : DN) : t (dnAction g x) = dnAction g (t x) := by
    apply e.injective
    change e (e.symm (f (e (dnAction g x)))) = _
    rw [e.apply_symm_apply,he,hf,he]
    simp [t]
  obtain ⟨c,hc⟩ := dn_commuting_scalar t ht
  refine ⟨c,?_⟩
  apply _root_.TensorProduct.ext'
  intro u v
  have h := LinearMap.congr_fun hc (v ⊗ₜ[ZMod 2] u)
  have hh := congrArg e h
  simpa only [t,LinearMap.comp_apply,LinearEquiv.coe_coe,e.apply_symm_apply,
    e,_root_.TensorProduct.comm_tmul,scalarND,scalarDN,_root_.TensorProduct.map_tmul,
    Module.End.one_apply,scalarNatural,LinearMap.coe_restrictScalars,
    LinearMap.lsmul_apply] using hh

lemma dn_to_nd_zero (f : DN →ₗ[ZMod 2] ND)
    (hf : ∀ (g : SL × SL) v, f (dnAction g v) = ndAction g (f v)) : f = 0 := by
  apply _root_.TensorProduct.ext'
  intro u v
  apply contractR_ext
  intro l
  let t : Deleted →ₗ[ZMod 2] Natural :=
    (contractR l).comp (f.comp ((_root_.TensorProduct.mk (ZMod 2) Deleted Natural).flip v))
  have ht (g : SL) (u : Deleted) : t (δ g u) = ν g (t u) := by
    change contractR l (f (δ g u ⊗ₜ[ZMod 2] v)) = _
    have he : δ g u ⊗ₜ[ZMod 2] v = dnAction (g,1) (u ⊗ₜ[ZMod 2] v) := by
      change _ = δ g u ⊗ₜ[ZMod 2] ν 1 v
      simp
    rw [he,hf]
    change contractR l (_root_.TensorProduct.map (ν g) (δ 1) (f (u ⊗ₜ[ZMod 2] v))) = _
    rw [map_one]
    exact contractR_left l (ν g) _
  have hz := LinearMap.congr_fun (deleted_to_natural_zero t ht) u
  change contractR l (f (u ⊗ₜ[ZMod 2] v)) = 0 at hz
  simpa only [LinearMap.zero_apply,map_zero] using hz

lemma nd_to_dn_zero (f : ND →ₗ[ZMod 2] DN)
    (hf : ∀ (g : SL × SL) v, f (ndAction g v) = dnAction g (f v)) : f = 0 := by
  apply _root_.TensorProduct.ext'
  intro u v
  apply contractR_ext
  intro l
  let t : Natural →ₗ[ZMod 2] Deleted :=
    (contractR l).comp (f.comp ((_root_.TensorProduct.mk (ZMod 2) Natural Deleted).flip v))
  have ht (g : SL) (u : Natural) : t (ν g u) = δ g (t u) := by
    change contractR l (f (ν g u ⊗ₜ[ZMod 2] v)) = _
    have he : ν g u ⊗ₜ[ZMod 2] v = ndAction (g,1) (u ⊗ₜ[ZMod 2] v) := by
      change _ = ν g u ⊗ₜ[ZMod 2] δ 1 v
      simp
    rw [he,hf]
    change contractR l (_root_.TensorProduct.map (δ g) (ν 1) (f (u ⊗ₜ[ZMod 2] v))) = _
    rw [map_one]
    exact contractR_left l (δ g) _
  have hz := LinearMap.congr_fun (natural_to_deleted_zero t ht) u
  change contractR l (f (u ⊗ₜ[ZMod 2] v)) = 0 at hz
  simpa only [LinearMap.zero_apply,map_zero] using hz

def scalarPair (c d : F) : Module.End (ZMod 2) Space :=
  (scalarND c).prodMap (scalarDN d)

/-- The full commuting algebra has exactly two independent F₄ scalar blocks. -/
lemma centralizer_blocks (f : Module.End (ZMod 2) Space)
    (hf : ∀ (g : SL × SL) v, f (action g v) = action g (f v)) :
    ∃ c d : F, f = scalarPair c d := by
  let p := LinearMap.fst (ZMod 2) ND DN
  let q := LinearMap.snd (ZMod 2) ND DN
  let i := LinearMap.inl (ZMod 2) ND DN
  let j := LinearMap.inr (ZMod 2) ND DN
  have hF (g : SL × SL) (u : ND) (v : DN) :
      f (ndAction g u,dnAction g v) =
        (ndAction g (f (u,v)).1,dnAction g (f (u,v)).2) := by
    rw [← action_special,hf,action_special]
  obtain ⟨c,hc⟩ := nd_commuting_scalar (p.comp (f.comp i)) (fun g v => by
    simpa [p,i] using congrArg Prod.fst (hF g v 0))
  obtain ⟨d,hd⟩ := dn_commuting_scalar (q.comp (f.comp j)) (fun g v => by
    simpa [q,j] using congrArg Prod.snd (hF g 0 v))
  have hb := dn_to_nd_zero (p.comp (f.comp j)) (fun g v => by
    simpa [p,j] using congrArg Prod.fst (hF g 0 v))
  have ha := nd_to_dn_zero (q.comp (f.comp i)) (fun g v => by
    simpa [q,i] using congrArg Prod.snd (hF g v 0))
  refine ⟨c,d,?_⟩
  apply LinearMap.ext
  rintro ⟨u,v⟩
  have hadd : f (u,v) = f (u,0) + f (0,v) := by
    simpa using f.map_add (u,0) (0,v)
  rw [hadd]
  apply Prod.ext
  · have hcu := LinearMap.congr_fun hc u
    have hbv := LinearMap.congr_fun hb v
    change (f (u,0)).1 = scalarND c u at hcu
    change (f (0,v)).1 = 0 at hbv
    change (f (u,0)).1 + (f (0,v)).1 = scalarND c u
    rw [hcu,hbv,add_zero]
  · have hdv := LinearMap.congr_fun hd v
    have hau := LinearMap.congr_fun ha u
    change (f (0,v)).2 = scalarDN d v at hdv
    change (f (u,0)).2 = 0 at hau
    change (f (u,0)).2 + (f (0,v)).2 = scalarDN d v
    rw [hau,hdv,zero_add]

lemma scalarND_mul (c d : F) : scalarND (c*d) = scalarND c * scalarND d := by
  apply _root_.TensorProduct.ext'
  intro u v
  simp [scalarND,scalarNatural,mul_smul]
  rw [smul_comm c d]
lemma scalarDN_mul (c d : F) : scalarDN (c*d) = scalarDN c * scalarDN d := by
  apply _root_.TensorProduct.ext'
  intro u v
  simp [scalarDN,scalarNatural,mul_smul]
  rw [smul_comm c d]
lemma scalarND_one : scalarND 1 = 1 := by
  apply _root_.TensorProduct.ext'
  intro u v
  simp [scalarND,scalarNatural]
lemma scalarDN_one : scalarDN 1 = 1 := by
  apply _root_.TensorProduct.ext'
  intro u v
  simp [scalarDN,scalarNatural]
lemma scalarPair_mul (c d c' d' : F) :
    scalarPair (c*c') (d*d') = scalarPair c d * scalarPair c' d' := by
  rw [scalarPair,scalarND_mul,scalarDN_mul]
  exact (LinearMap.prodMap_mul _ _ _ _).symm
lemma scalarPair_one : scalarPair 1 1 = 1 := by
  rw [scalarPair,scalarND_one,scalarDN_one,LinearMap.prodMap_one]

lemma centralizer_fourth (f : Module.End (ZMod 2) Space)
    (hf : ∀ (g : SL × SL) v, f (action g v) = action g (f v)) :
    f ^ 4 = f := by
  obtain ⟨c,d,rfl⟩ := centralizer_blocks f hf
  have h : ∀ n : ℕ, scalarPair c d ^ n = scalarPair (c^n) (d^n) := by
    intro n
    induction n with
    | zero => simp [scalarPair_one]
    | succ n ih => rw [pow_succ,ih,pow_succ,pow_succ,scalarPair_mul]
  rw [h,SL2FourNatural.pow_four,SL2FourNatural.pow_four]

/-- In particular no nonidentity involution centralizes the marked A₅² action. -/
lemma centralizer_involution_eq_one (f : Module.End (ZMod 2) Space)
    (hf : ∀ (g : SL × SL) v, f (action g v) = action g (f v))
    (h2 : f*f=1) : f=1 := by
  have h := centralizer_fourth f hf
  have h22 : f^2=1 := by simpa only [pow_two] using h2
  have h4 : f^4=1 := by rw [show 4=2*2 from rfl,pow_mul,h22,one_pow]
  exact h.symm.trans h4

/-- Binary tensor faithfulness, specialized to the actual two four-spaces. -/
lemma tensor_identity_factors (a : Module.End (ZMod 2) Natural)
    (b : Module.End (ZMod 2) Deleted) (ha : Function.Injective a)
    (hb : Function.Injective b)
    (h : ∀ u v, a u ⊗ₜ[ZMod 2] b v = u ⊗ₜ[ZMod 2] v) : a=1 ∧ b=1 := by
  let : Nontrivial Natural := Module.nontrivial_of_finrank_pos (by rw [finrank_natural]; decide)
  let : Nontrivial Deleted := Module.nontrivial_of_finrank_pos (by rw [finrank_deleted]; decide)
  obtain ⟨z,hz⟩ := exists_ne (0 : Deleted)
  have hbz : b z ≠ 0 := fun h => hz (hb (h.trans b.map_zero.symm))
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hbz
  have hae (u : Natural) : a u = l z • u := by
    have hh := congrArg (contractR l) (h u z)
    simpa only [contractR_tmul,hl,one_smul] using hh
  have hbinary : ∀ c : ZMod 2, c=0 ∨ c=1 := by decide
  have hlz : l z = 1 := by
    rcases hbinary (l z) with h0 | h1
    · obtain ⟨u,hu⟩ := exists_ne (0 : Natural)
      exact (hu (ha (by simpa only [h0,zero_smul,map_zero] using hae u))).elim
    · exact h1
  have ha1 : a=1 := by
    apply LinearMap.ext
    intro u
    simpa only [hlz,one_smul,Module.End.one_apply] using hae u
  refine ⟨ha1,?_⟩
  obtain ⟨u,hu⟩ := exists_ne (0 : Natural)
  obtain ⟨r,hr⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hu
  apply LinearMap.ext
  intro v
  have hh := congrArg (contractL r) (h u v)
  simpa only [ha1,Module.End.one_apply,contractL_tmul,hr,one_smul] using hh

lemma first_injective : Function.Injective first := by
  apply (injective_iff_map_eq_one first).mpr
  intro g hg
  have hh := tensor_identity_factors (naturalAction g.1) (deletedAction g.2)
    (naturalAction.apply_bijective g.1).injective (deletedAction.apply_bijective g.2).injective
    (fun u v => LinearMap.congr_fun hg (u ⊗ₜ[ZMod 2] v))
  apply Prod.ext
  · apply naturalAction_injective
    simpa only [Prod.fst_one,map_one] using hh.1
  · by_contra hn
    have hd := deleted_displacement_pos g.2 hn
    rw [hh.2] at hd
    simp [Representation.BinaryOffender.NaturalTensor.operatorFixedCodim] at hd

lemma extendedAction_injective : Function.Injective extendedAction := by
  intro g h he
  apply first_injective
  apply LinearMap.ext
  intro u
  exact congrArg Prod.fst (LinearMap.congr_fun he (u,0))

lemma action_injective : Function.Injective action := by
  intro g h he
  have hmark := extendedAction_injective he
  apply Prod.ext
  · exact specialFiveLines_injective (congrArg Prod.fst hmark)
  · exact specialFiveLines_injective (congrArg Prod.snd hmark)
end Representation.AlternatingFiveMovedPair.Mixed
