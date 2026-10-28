module

public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction

/-!
# Pulling back a central extension and descending local sections

The fiber product of two homomorphisms retains the original extension kernel.
A section over a subgroup of the other source descends to its image whenever
the second homomorphism is injective on that subgroup. All projections and
section identities remain literal maps.

Source application: the defining-prime kernel calculation for PSU₄ in
Aschbacher–Smith A.2.17, via the actual SU₄ positive subgroup.
-/

open Subgroup PerfectCentralCovering
namespace CentralExtension

variable {E A B : Type*} [Group E] [Group A] [Group B]

public def pullback (f : E →* B) (g : A →* B) : Subgroup (E × A) :=
  (f.comp (MonoidHom.fst E A)).eqLocus (g.comp (MonoidHom.snd E A))

public def pullbackLeft (f : E →* B) (g : A →* B) : pullback f g →* E :=
  (MonoidHom.fst E A).comp (pullback f g).subtype

public def pullbackRight (f : E →* B) (g : A →* B) : pullback f g →* A :=
  (MonoidHom.snd E A).comp (pullback f g).subtype

public theorem pullbackRight_surjective (f : E →* B) (g : A →* B)
    (hf : Function.Surjective f) : Function.Surjective (pullbackRight f g) := by
  intro a
  obtain ⟨e,he⟩ := hf (g a)
  exact ⟨⟨(e,a),he⟩,rfl⟩

public theorem pullbackRight_central (f : E →* B) (g : A →* B)
    (hc : f.ker ≤ center E) : (pullbackRight f g).ker ≤ center (pullback f g) := by
  intro z hz
  have hzA : z.val.2=1 := hz
  have hzE : z.val.1 ∈ f.ker := by
    change f z.val.1=1
    calc
      _ = g z.val.2 := z.property
      _ = 1 := by rw [hzA,map_one]
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact mem_center_iff.mp (hc hzE) x.val.1
  · change x.val.2*z.val.2=z.val.2*x.val.2
    rw [hzA,mul_one,one_mul]

public noncomputable def pullbackKernelEquiv (f : E →* B) (g : A →* B) :
    (pullbackRight f g).ker ≃* f.ker where
  toFun z := ⟨z.val.val.1,by
    change f z.val.val.1=1
    have hz : z.val.val.2=1 := z.property
    calc
      _ = g z.val.val.2 := z.val.property
      _ = 1 := by rw [hz,map_one]⟩
  invFun z := ⟨⟨(z.val,1),by change f z.val=g 1; rw [map_one]; exact z.property⟩,rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact z.property.symm
  right_inv z := rfl
  map_mul' x y := rfl

public theorem exists_section_on_image_of_pullback
    (f : E →* B) (g : A →* B) (P : Subgroup A)
    (hinj : Function.Injective (g.comp P.subtype))
    (s : P →* pullback f g) (hs : (pullbackRight f g).comp s=P.subtype) :
    ∃ t : P.map g →* E, f.comp t=(P.map g).subtype := by
  let q : P →* P.map g := (g.comp P.subtype).codRestrict (P.map g)
    (fun x => ⟨x.val,x.property,rfl⟩)
  have hq : Function.Bijective q := by
    constructor
    · intro x y he
      exact hinj (congrArg Subtype.val he)
    · rintro ⟨b,⟨a,ha,rfl⟩⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  let e : P ≃* P.map g := MulEquiv.ofBijective q hq
  refine ⟨(pullbackLeft f g).comp (s.comp e.symm.toMonoidHom),?_⟩
  ext x
  change f (s (e.symm x)).val.1=x.val
  calc
    _ = g (s (e.symm x)).val.2 := (s (e.symm x)).property
    _ = g (e.symm x).val := congrArg g (DFunLike.congr_fun hs (e.symm x))
    _ = x.val := congrArg Subtype.val (e.apply_symm_apply x)

end CentralExtension
