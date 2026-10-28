module
public import Theory.Representation.SL2OrthogonalCover.FixedCommutatorRows
public import Theory.Representation.SL2OrthogonalCover.Sylow
/-!
# Fixed commutator rows at the actual Sylow root

Two distinct nonidentity elements of any Sylow two-subgroup of SL₂ have
independent displacement lines spanning its fixed plane. Trace-one averaging
lifts their fixed displacements to fixed vectors. One nonidentity fixed root
always supplies a nonsingular fixed displacement. The group adapters preserve
the original root lifts and apply directly to subgroup commutators.

Source: Aschbacher–Smith, I.2.3 and the inside cases of 2.4.21, printed p.536.
-/

public section
noncomputable section
namespace Representation.SL2OrthogonalCover
open Matrix Representation.OneCohomology
open scoped commutatorElement
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Algebra (ZMod 2) F] in
theorem sylow_two_displacements (P : Sylow 2 (SL F)) (g h : SL F)
    (hg : g∈P) (hh : h∈P) (hg1 : g≠1) (hh1 : h≠1) (hgh : g≠h)
    (v : Space F) (hv : v∈fixed ((action (F:=F)).comp P.toSubgroup.subtype)) :
    ∃ u w : Space F, v=(action g u-u)+(action h w-w) := by
  have hgdata := sylow_displacement_geometry P g hg hg1
  have hhdata := sylow_displacement_geometry P h hh hh1
  have hdis := sylow_displacements_disjoint P g h hg hh hg1 hh1 hgh
  have hdim : Module.finrank F (movedSpace g ⊔ movedSpace h : Submodule F (Space F))=2 := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq (movedSpace g) (movedSpace h)
    rw [hdis.eq_bot,finrank_bot,add_zero,hgdata.1,hhdata.1] at he
    exact he
  have hfixdim : Module.finrank F (fixed ((action (F:=F)).comp P.toSubgroup.subtype))=2 := by
    obtain ⟨A,hA,he,hdis,_⟩ := sylow_fixed_geometry P
    rw [he]
    have hd := Submodule.finrank_sup_add_finrank_inf_eq A (form (F:=F)).polarBilin.ker
    rw [hdis.eq_bot,finrank_bot,add_zero,hA,radical_dimension] at hd
    exact hd
  have he : movedSpace g ⊔ movedSpace h = fixed ((action (F:=F)).comp P.toSubgroup.subtype) :=
    Submodule.eq_of_le_of_finrank_eq (sup_le hgdata.2.1 hhdata.2.1) (hdim.trans hfixdim.symm)
  have hv' : v∈movedSpace g⊔movedSpace h := he.symm ▸ hv
  obtain ⟨x,⟨u,hu⟩,y,⟨w,hw⟩,hxy⟩ := Submodule.mem_sup.mp hv'
  exact ⟨u,w,by rw [←hxy,←hu,←hw]; rfl⟩

theorem fixed_sylow_two_displacements
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hσne : σ≠RingEquiv.refl F)
    (E : Space F ≃ₗ[ZMod 2] Space F) (hE : Function.Involutive E)
    (hsemi : ∀c v,E (c•v)=σ c•E v)
    (P : Sylow 2 (SL F)) (g h : SL F)
    (hg : g∈P) (hh : h∈P) (hg1 : g≠1) (hh1 : h≠1) (hgh : g≠h)
    (hEg : ∀v,E (action g v)=action g (E v))
    (hEh : ∀v,E (action h v)=action h (E v))
    (v : Space F) (hv : v∈fixed ((action (F:=F)).comp P.toSubgroup.subtype)) (hEv : E v=v) :
    ∃u w : Space F,E u=u∧E w=w∧v=(action g u-u)+(action h w-w) := by
  obtain ⟨c,hc⟩ := (Theory.PSL2.fixed_iff_exists_add_conjugate σ hσ hσne (1:F)).mp (map_one σ)
  obtain ⟨u,w,hvw⟩ := sylow_two_displacements P g h hg hh hg1 hh1 hgh v hv
  refine ⟨c•u+E (c•u),c•w+E (c•w),by rw [map_add,hE,add_comm],by rw [map_add,hE,add_comm],?_⟩
  have hd (k : SL F) (hk : ∀v,E (action k v)=action k (E v)) (u : Space F) :
      action k (c•u+E (c•u))-(c•u+E (c•u))=c•(action k u-u)+E (c•(action k u-u)) := by
    simp only [map_add]
    rw [←hk]
    simp only [map_smul,map_sub,smul_sub]
    abel
  rw [hd g hEg,hd h hEh]
  calc
    v=(c+σ c)•v := by rw [hc,one_smul]
    _=c•v+E (c•v) := by rw [hsemi,hEv,add_smul]
    _=_ := by rw [hvw,smul_add,map_add]; abel

theorem fixed_sylow_mem_commutator {G : Type*} [Group G]
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hσne : σ≠RingEquiv.refl F)
    (E : Space F ≃ₗ[ZMod 2] Space F) (hE : Function.Involutive E)
    (hsemi : ∀c v,E (c•v)=σ c•E v)
    (P : Sylow 2 (SL F)) (g h : SL F)
    (hg : g∈P) (hh : h∈P) (hg1 : g≠1) (hh1 : h≠1) (hgh : g≠h)
    (hEg : ∀v,E (action g v)=action g (E v))
    (hEh : ∀v,E (action h v)=action h (E v))
    (I : Subgroup G) (q : Multiplicative (Space F)→*G)
    (hq : ∀v,E v=v→q (Multiplicative.ofAdd v)∈I)
    (r t : G) (hr : r∈I) (ht : t∈I)
    (hactr : ∀v,q (Multiplicative.ofAdd (action g v))=r*q (Multiplicative.ofAdd v)*r⁻¹)
    (hactt : ∀v,q (Multiplicative.ofAdd (action h v))=t*q (Multiplicative.ofAdd v)*t⁻¹)
    (v : Space F) (hv : v∈fixed ((action (F:=F)).comp P.toSubgroup.subtype)) (hEv : E v=v) :
    q (Multiplicative.ofAdd v)∈⁅I,I⁆ := by
  obtain ⟨u,w,hu,hw,hvw⟩ := fixed_sylow_two_displacements σ hσ hσne E hE hsemi P g h hg hh hg1 hh1 hgh hEg hEh v hv hEv
  have hgr : q (Multiplicative.ofAdd (action g u-u))=⁅r,q (Multiplicative.ofAdd u)⁆ := by
    rw [ofAdd_sub,map_div,hactr,div_eq_mul_inv]
    rfl
  have hht : q (Multiplicative.ofAdd (action h w-w))=⁅t,q (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,map_div,hactt,div_eq_mul_inv]
    rfl
  rw [hvw]
  change q (Multiplicative.ofAdd (action g u-u)*Multiplicative.ofAdd (action h w-w))∈_
  rw [map_mul,hgr,hht]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hr (hq u hu))
    (Subgroup.commutator_mem_commutator ht (hq w hw))
theorem exists_fixed_sylow_displacement
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hσne : σ≠RingEquiv.refl F)
    (E : Space F ≃ₗ[ZMod 2] Space F) (hE : Function.Involutive E)
    (hsemi : ∀c v,E (c•v)=σ c•E v)
    (P : Sylow 2 (SL F)) (g : SL F) (hg : g∈P) (hg1 : g≠1)
    (hEg : ∀v,E (action g v)=action g (E v)) :
    ∃u : Space F,E u=u ∧ form (action g u-u)≠0 := by
  have hdata := sylow_displacement_geometry P g hg hg1
  have hn : movedSpace g≠⊥ := by
    intro he
    have hh := hdata.1
    rw [he,finrank_bot] at hh
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hev : E v∈movedSpace g := by
    obtain ⟨w,hw⟩ := hv
    change action g w-w=v at hw
    rw [←hw,map_sub,hEg]
    exact ⟨E w,rfl⟩
  have hex : ∃x : Space F,x∈movedSpace g ∧ x≠0 ∧ E x=x := by
    by_cases hz : v+E v=0
    · refine ⟨v,hv,hv0,?_⟩
      have hh := congrArg (fun x : Space F => x-v) hz
      have hneg : -v=v := by ext i; exact CharTwo.neg_eq _
      simpa only [add_sub_cancel_left,zero_sub,hneg] using hh
    · exact ⟨v+E v,(movedSpace g).add_mem hv hev,hz,by rw [map_add,hE,add_comm]⟩
  obtain ⟨x,hx,hx0,hEx⟩ := hex
  obtain ⟨w,hw⟩ := hx
  change action g w-w=x at hw
  obtain ⟨c,hc⟩ := (Theory.PSL2.fixed_iff_exists_add_conjugate σ hσ hσne (1:F)).mp (map_one σ)
  have hdelta : action g (c•w+E (c•w))-(c•w+E (c•w))=x := by
    have he : action g (E (c•w))-E (c•w)=σ c•x := by
      rw [←hEg,←map_sub,map_smul,←smul_sub,hw,hsemi,hEx]
    calc
      _=c•(action g w-w)+(action g (E (c•w))-E (c•w)) := by
        rw [map_add,map_smul,smul_sub]; abel
      _=x := by rw [hw,he,←add_smul,hc,one_smul]
  exact ⟨c•w+E (c•w),by rw [map_add,hE,add_comm],hdelta ▸ hdata.2.2.1 x ⟨w,hw⟩ hx0⟩

theorem exists_fixed_sylow_commutator {G : Type*} [Group G]
    (σ : F ≃+* F) (hσ : Function.Involutive σ) (hσne : σ≠RingEquiv.refl F)
    (E : Space F ≃ₗ[ZMod 2] Space F) (hE : Function.Involutive E)
    (hsemi : ∀c v,E (c•v)=σ c•E v)
    (P : Sylow 2 (SL F)) (g : SL F) (hg : g∈P) (hg1 : g≠1)
    (hEg : ∀v,E (action g v)=action g (E v))
    (I : Subgroup G) (q : Multiplicative (Space F)→*G)
    (hq : ∀v,E v=v→q (Multiplicative.ofAdd v)∈I)
    (r : G) (hr : r∈I)
    (hact : ∀v,q (Multiplicative.ofAdd (action g v))=r*q (Multiplicative.ofAdd v)*r⁻¹) :
    ∃v : Space F,E v=v ∧ v∈movedSpace g ∧ form v≠0 ∧ q (Multiplicative.ofAdd v)∈⁅I,I⁆ := by
  obtain ⟨u,hu,hform⟩ := exists_fixed_sylow_displacement σ hσ hσne E hE hsemi P g hg hg1 hEg
  refine ⟨action g u-u,by rw [map_sub,hEg,hu],⟨u,rfl⟩,hform,?_⟩
  have he : q (Multiplicative.ofAdd (action g u-u))=⁅r,q (Multiplicative.ofAdd u)⁆ := by
    rw [ofAdd_sub,map_div,hact,div_eq_mul_inv]
    rfl
  rw [he]
  exact Subgroup.commutator_mem_commutator hr (hq u hu)

end Representation.SL2OrthogonalCover
