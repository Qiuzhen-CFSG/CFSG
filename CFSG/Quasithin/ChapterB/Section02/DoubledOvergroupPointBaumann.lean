module
public import Theory.Representation.PSL3Two.DoubledNormalizerPoint
public import CFSG.Quasithin.ChapterB.Section02.DoubledPointBaumann
public import Theory.Representation.NormalElementaryQuotient.OriginalAction

/-!
# Baumann control for the full doubled-natural point radical

A normal component marked as two identical natural SL₃(2) modules puts the
whole action image in the full doubled-natural normalizer. The model's
point-radical exclusion therefore forces every maximum elementary subgroup
of the original point radical to centralize the module. If the overgroup
modulo the component is a two-group and its two-core centralizes the module,
the exact component kernel also makes the whole module centralizer a
two-group. B.2.10 now identifies the original radical's Thompson and Baumann
subgroups with those of the overgroup's two-core.

The intended consumer is O₂(L₁T) inside KT in the original augmentation
branch of Aschbacher–Smith 13.4.10(4), printed p.909. The proof permits
nontrivial actions outside K and does not assume a containing-component or
short-block conclusion.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB
open Representation.SL3DoubledNaturalOffenders
variable {H : Type*} [Group H] [Finite H]

/-- A doubled component controls the full point radical, including actors
outside the component. -/
theorem doubled_overgroup_point_thompson
    (K U : Subgroup H) [K.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (q : K →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : ∀ (k : K) (u : U), (e (MulAut.conjNormal k.val u)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (e u).toAdd)
    (w : U) (hw : w ≠ 1) (S : Sylow 2 K)
    (hSw : (S : Subgroup K).map K.subtype ≤ centralizer ({w.val} : Set H)) :
    elementaryAbelianMaxJ ((centralizer ({w.val} : Set H)).pCoreIn 2) ≤
      centralizer (U : Set H) := by
  let F := ZMod 2
  let : Finite (Module.End F (Space F)) := Finite.of_injective
    (fun a : Module.End F (Space F) => (a : Space F → Space F)) DFunLike.coe_injective
  let ea : Additive U ≃+ (BinaryLinearThree.Vector × BinaryLinearThree.Vector) := {
    toFun := fun u => (e u.toMul).toAdd
    invFun := fun v => Additive.ofMul (e.symm (Multiplicative.ofAdd v))
    left_inv := fun u => e.symm_apply_apply u
    right_inv := fun v => e.apply_symm_apply (Multiplicative.ofAdd v)
    map_add' := fun u v => e.map_mul u.toMul v.toMul }
  let b0 : Additive U ≃ₗ[ZMod 2] (BinaryLinearThree.Vector × BinaryLinearThree.Vector) := {
    __ := ea
    map_smul' := ZMod.map_smul ea }
  let b := b0.trans (LinearEquiv.finTwoArrow (ZMod 2) BinaryLinearThree.Vector).symm
  let σ := Representation.NormalElementaryQuotient.originalAction U
  let τ : Representation (ZMod 2) H (Space F) := b.conjRingEquiv.toMonoidHom.comp σ
  let f := τ.asGroupHom
  let μ := (representation F).asGroupHom
  have heval (h : H) (u : U) :
      action F (f h) (b (Additive.ofMul u)) = b (Additive.ofMul (MulAut.conjNormal h u)) := by
    change b (σ h (b.symm (b (Additive.ofMul u)))) = _
    rw [b.symm_apply_apply]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Representation.NormalElementaryQuotient.originalAction_apply U h (Additive.ofMul u)
  have hk : f.ker = centralizer (U : Set H) := by
    rw [←Representation.NormalElementaryQuotient.originalAction_kernel U]
    ext h
    change f h = 1 ↔ σ h = 1
    constructor
    · intro hh
      apply b.conjRingEquiv.injective
      have hhh := congrArg Units.val hh
      change b.conjRingEquiv (σ h) = 1 at hhh
      simpa using hhh
    · intro hh
      apply Units.ext
      change b.conjRingEquiv (σ h) = 1
      rw [hh,map_one]
  have hfk (k : K) : f k.val = μ (q k) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨u,hu⟩ := b.surjective v
    rw [←hu]
    change action F (f k.val) (b u) = action F (μ (q k)) (b u)
    rw [show action F (f k.val) (b u) = _ from heval k.val u.toMul]
    have hh := he k u.toMul
    funext i
    fin_cases i
    · exact congrArg Prod.fst hh
    · exact congrArg Prod.snd hh
  have hKf : K.map f = component F := by
    apply le_antisymm
    · rintro a ⟨k,hk,rfl⟩
      exact ⟨q ⟨k,hk⟩,(hfk ⟨k,hk⟩).symm⟩
    · rintro a ⟨g,rfl⟩
      obtain ⟨k,rfl⟩ := hq g
      exact ⟨k.val,k.property,hfk k⟩
  let D := f.range
  have hDN : D ≤ normalizer F := by
    rw [show normalizer F = Subgroup.normalizer (component F : Set (Ambient F)) from rfl,←hKf]
    rintro a ⟨h,rfl⟩
    exact K.le_normalizer_map f (mem_map_of_mem f (le_normalizer_of_normal (mem_top h)))
  have hCD : component F ≤ D := hKf ▸ (map_le_range f K)
  let v := (e w).toAdd
  have hv : v ≠ 0 := by
    intro hh
    apply hw
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [map_one]
    exact hh
  let S₀ := S.mapSurjective hq
  have hfix (a : S₀) : (BinaryLinearThree.W.prod BinaryLinearThree.W) a.val v = v := by
    obtain ⟨k,hk,hka⟩ := a.property
    rw [←hka,←he]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp
      (hSw (mem_map_of_mem K.subtype hk)))
  obtain ⟨v₀,hv₀,hpoint⟩ := BinaryLinearThree.doubled_sylow_fixed_naturalPoint S₀ v hv hfix
  let v' := b (Additive.ofMul w)
  have hpoint' : (binaryPoint v').comap μ = BinaryLinearThree.naturalPoint v₀ := by
    rw [←hpoint]
    ext g
    change (fun i => (g.val).mulVec (v' i)) = v' ↔ _
    rw [mem_inf,BinaryLinearThree.OrbitStabilizers.mem_natural,
      BinaryLinearThree.OrbitStabilizers.mem_natural]
    constructor
    · intro hh
      exact ⟨congrFun hh 0,congrFun hh 1⟩
    · rintro ⟨h1,h2⟩
      funext i
      fin_cases i
      · exact h1
      · exact h2
  let P := centralizer ({w.val} : Set H)
  let R := P.pCoreIn 2
  have hmem (h : H) : f h ∈ binaryPoint v' ↔ h ∈ P := by
    change action F (f h) (b (Additive.ofMul w)) = b (Additive.ofMul w) ↔ _
    rw [heval,b.injective.eq_iff,Additive.ofMul.injective.eq_iff,Subtype.ext_iff]
    change h*w.val*h⁻¹ = w.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  have hPf : P.map f = D ⊓ binaryPoint v' := by
    ext a
    constructor
    · rintro ⟨h,hh,rfl⟩
      exact ⟨⟨h,rfl⟩,(hmem h).mpr hh⟩
    · rintro ⟨⟨h,rfl⟩,hh⟩
      exact mem_map_of_mem f ((hmem h).mp hh)
  have hRf : R.map f ≤ (D ⊓ binaryPoint v').pCoreIn 2 := by
    rw [←hPf]
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 P).map f) (map_mono (pCoreIn_le 2 P))
    exact (map_mono (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))).trans (R.le_normalizer_map f)
  have hUR : U ≤ R := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
    (fun u hu => mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) w))) (by rw [normalizer_eq_top];exact le_top)
  have hfixed (A : Subgroup H) :
      Nat.card (U ⊓ centralizer (A : Set H) : Subgroup H) =
        Nat.card (fixedSpace (action F) (A.map f)) := by
    apply Nat.card_congr
    exact {
      toFun := fun u => ⟨b (Additive.ofMul ⟨u.val,u.property.1⟩),fun a => by
        obtain ⟨h,hh,hha⟩ := a.property
        change action F a.val _ = _
        rw [←hha,heval]
        congr 1
        apply Additive.toMul.injective
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (u.property.2 h hh)⟩
      invFun := fun v => ⟨(b.symm v.val).toMul.val,(b.symm v.val).toMul.property,by
        intro h hh
        have hv := v.property ⟨f h,mem_map_of_mem f hh⟩
        have hbv := b.apply_symm_apply v.val
        change action F (f h) v.val = v.val at hv
        rw [←hbv] at hv
        change action F (f h) (b (Additive.ofMul (b.symm v.val).toMul)) = _ at hv
        rw [heval] at hv
        have hv' := congrArg (fun x => (b.symm x).toMul.val) hv
        simp only [b.symm_apply_apply] at hv'
        exact mul_inv_eq_iff_eq_mul.mp hv' ⟩
      left_inv := fun u => by apply Subtype.ext; simp
      right_inv := fun v => by apply Subtype.ext; simp }
  apply sSup_le
  intro A hA
  rw [←hk]
  apply (Subgroup.map_eq_bot_iff _).mp
  by_contra hn
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hAe : IsElementaryTwo (A.map f) := ⟨hn,inferInstance⟩
  have hAo : IsOffender (action F) (A.map f) := by
    apply (EndFieldTransfer.offender_iff_card _ _ hAe).mpr
    have hh := maxElementary_card_le_fixed_mul_image R U A hUR hA f hk
    rw [hfixed] at hh
    have hcard : Nat.card U = Nat.card (Space F) := Nat.card_congr b.toEquiv
    rwa [hcard,mul_comm] at hh
  exact hn (binary_point_radical_offender_eq_bot D hDN hCD v' v₀ hv₀ hpoint'
    (A.map f) ((map_mono hA.1).trans hRf) hAo)

omit [Finite H] in
/-- A two-group extension of the marked component has no additional odd
centralizer of its doubled module. -/
theorem doubled_overgroup_centralizer_eq_core
    (K U : Subgroup H) [K.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (q : K →* BinaryLinearThree.Group) (hk : q.ker = pCore 2 K)
    (e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : ∀ (k : K) (u : U), (e (MulAut.conjNormal k.val u)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (e u).toAdd)
    (hquot : IsPGroup 2 (H ⧸ K))
    (hcore : pCore 2 H ≤ centralizer (U : Set H)) :
    centralizer (U : Set H) = pCore 2 H := by
  let C := centralizer (U : Set H)
  have hp : IsPGroup 2 C := by
    intro c
    obtain ⟨n,hn⟩ := hquot (QuotientGroup.mk' K c.val)
    have hcn : c.val ^ (2 ^ n) ∈ K := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' K (c.val ^ (2 ^ n)) = 1
      simpa only [map_pow] using hn
    let k : K := ⟨c.val ^ (2 ^ n),hcn⟩
    have hck : k.val ∈ C := C.pow_mem c.property _
    have hqk : q k = 1 := by
      apply BinaryLinearThree.natural_injective
      apply LinearMap.ext
      intro x
      let u := e.symm (Multiplicative.ofAdd (x,0))
      have hconj : MulAut.conjNormal k.val u = u := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (hck u.val u.property).symm
      have hh := he k u
      rw [hconj,e.apply_symm_apply] at hh
      rw [map_one]
      exact (congrArg Prod.fst hh).symm
    have hkcore : k ∈ pCore 2 K := hk ▸ (show k ∈ q.ker from hqk)
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := K)) ⟨k,hkcore⟩
    have hh : (c.val ^ (2 ^ n)) ^ (2 ^ m) = 1 :=
      congrArg (fun a : pCore 2 K => a.val.val) hm
    refine ⟨n+m,Subtype.ext ?_⟩
    change c.val ^ (2 ^ (n+m)) = 1
    simpa only [pow_add,pow_mul] using hh
  exact le_antisymm (le_sSup ⟨inferInstance,hp⟩) hcore

/-- The full point radical has the Thompson and Baumann subgroups of the
ambient two-core, so its Baumann subgroup is normal in the whole overgroup. -/
theorem doubled_overgroup_point_baumann
    (K U : Subgroup H) [K.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (q : K →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 K)
    (e : U ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : ∀ (k : K) (u : U), (e (MulAut.conjNormal k.val u)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (e u).toAdd)
    (hquot : IsPGroup 2 (H ⧸ K))
    (hcore : pCore 2 H ≤ centralizer (U : Set H))
    (w : U) (hw : w ≠ 1) (S : Sylow 2 K)
    (hSw : (S : Subgroup K).map K.subtype ≤ centralizer ({w.val} : Set H)) :
    let R := (centralizer ({w.val} : Set H)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 H) ∧
      baumann R = baumann (pCore 2 H) ∧ (baumann R).Normal := by
  let P := centralizer ({w.val} : Set H)
  let R := P.pCoreIn 2
  have hC := doubled_overgroup_centralizer_eq_core K U q hk e he hquot hcore
  have hQP : pCore 2 H ≤ P := by
    rw [←hC]
    exact fun h hh => mem_centralizer_singleton_iff.mpr (hh w.val w.property).symm
  have hQR : pCore 2 H ≤ R :=
    le_pCoreIn_of_normalizes pCore_isPGroup hQP (by rw [normalizer_eq_top];exact le_top)
  have hUQ : U ≤ pCore 2 H := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hUR : U ≤ R := hUQ.trans hQR
  have hRC : pCore 2 H = R ⊓ centralizer (U : Set H) := by
    rw [hC,inf_eq_right.mpr hQR]
  have hJ := doubled_overgroup_point_thompson K U q hq e he w hw S hSw
  have hb := lemma_B_2_10_centralizing U R hUR hQR hRC (by rwa [thompsonJ_zero])
  exact ⟨by simpa only [thompsonJ_zero] using hb.1,hb.2.1,hb.2.2.2⟩
end CFSG.Quasithin.ChapterB
