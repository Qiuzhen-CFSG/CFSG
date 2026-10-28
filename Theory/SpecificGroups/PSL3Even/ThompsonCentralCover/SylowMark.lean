module
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover.CommutatorRows
/-! # Literal marks on component Sylow covers
Sylow conjugacy identifies the image of the actual covering map with the
matrix unipotent group. The mark retains its exact kernel and elementary
full preimages. Source: Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Even.UnipotentGeometry
open PSL3.LinearThree
variable {E F:Type*} [Group E] [Finite E] [Field F] [Finite F]
theorem exists_sylow_cover_mark
    (α:E→*PSL(3,F)) (hα:Function.Surjective α)
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap α))
    {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n) (S:Sylow 2 E) :
    ∃f:S→*U F, Function.Surjective f ∧ f.ker=α.ker.subgroupOf S ∧
      ∀W:Subgroup (U F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap f) := by
  let P:=S.mapSurjective (f:=α) hα
  let eU:U F≃*P:=(unipotentEquiv F).trans (Sylow.equiv (unipotentSylow F hn hF) P)
  let r:S→*P:={
    toFun x:=⟨α x,mem_map_of_mem α x.property⟩
    map_one':=Subtype.ext (map_one α)
    map_mul' x y:=Subtype.ext (map_mul α (x:E) (y:E)) }
  have hr:Function.Surjective r:=by
    rintro ⟨y,⟨x,hx,hxy⟩⟩
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  let f:S→*U F:=eU.symm.toMonoidHom.comp r
  have hf:Function.Surjective f:=eU.symm.surjective.comp hr
  let j:U F→*PSL(3,F):=(P:Subgroup PSL(3,F)).subtype.comp eU.toMonoidHom
  have hj (x:S):j (f x)=α x:=by
    change (eU (eU.symm (r x)):PSL(3,F))=_
    rw [eU.apply_symm_apply]
    rfl
  have hpre (V:Subgroup (U F)) [IsElementaryAbelian 2 V] : IsElementaryAbelian 2 (V.comap f):=by
    let W:=V.map j
    let : IsElementaryAbelian 2 W:=IsElementaryAbelian.map j
    let : IsElementaryAbelian 2 (W.comap α):=hlift W inferInstance
    let a:V.comap f→*W.comap α:={
      toFun x:=⟨x.val.val,by
        change α x.val∈W
        rw [←hj]
        exact mem_map_of_mem j x.property⟩
      map_one':=rfl
      map_mul' _ _:=rfl }
    apply IsElementaryAbelian.of_injective a
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z:W.comap α=>(z:E)) h))
  have hker:f.ker=α.ker.subgroupOf S:=by
    ext x
    change f x=1 ↔ α x=1
    constructor
    · intro hx
      rw [←hj,hx,map_one]
    · intro hx
      change eU.symm (r x)=1
      rw [show r x=1 from Subtype.ext hx,map_one]
  exact ⟨f,hf,hker,fun W hW=>by let :=hW;exact hpre W⟩
end Matrix.PSL3Even.UnipotentGeometry
