module
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.ConjugateLayerExchange
/-!
# An internal conjugate pair over a plane core

Two abelian conjugates centralize their intersection. If a normalizer of the
first conjugate moves a plane into that intersection, and the first subgroup
lies in the plane normalizer's two-core, the whole internally conjugate pair
is a two-group. The proof retains the actual conjugator and the ambient
subgroups. This is the group-theoretic contradiction in Aschbacher–Smith
13.3.18, printed p.895.
-/

public section
namespace Subgroup
open scoped IsMulCommutative
variable {G:Type*} [Group G]

/-- A source plane contained in a conjugated intersection forces an internal
abelian pair into the plane normalizer's two-core. -/
theorem pair_isTwo_of_conjugate_intersection_plane
    (V B:Subgroup G) [IsMulCommutative V] (g n:G)
    (hg:g∈V⊔V.map (MulAut.conj g).toMonoidHom)
    (hn:n∈normalizer (V:Set G))
    (hB:B≤(V⊓V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom)
    (hcore:V≤(normalizer (B:Set G)).pCoreIn 2) :
    IsPGroup 2 (V⊔V.map (MulAut.conj g).toMonoidHom:Subgroup G) := by
  let W:=V.map (MulAut.conj g).toMonoidHom
  let I:=V⊔W
  let f: G→*G:=(MulAut.conj n).toMonoidHom
  let N:=normalizer (B:Set G)
  let K:=N.pCoreIn 2
  let :IsMulCommutative W:=inferInstanceAs (IsMulCommutative (V.map (MulAut.conj g).toMonoidHom))
  have hIC:I≤centralizer (V⊓W:Set G) := sup_le
    ((le_centralizer V).trans (centralizer_le inf_le_left))
    ((le_centralizer W).trans (centralizer_le inf_le_right))
  have hIN:I.map f≤N := by
    apply le_trans _ (centralizer_le_normalizer (B:Set G))
    rintro _ ⟨i,hi,rfl⟩ b hb
    obtain ⟨a,ha,rfl⟩:=hB hb
    simpa only [map_mul] using congrArg f (hIC hi a ha)
  have hVn:V.map f=V:=mem_normalizer_iff_map_conj_eq.mp hn
  have hfg:f g∈N:=hIN (mem_map_of_mem f hg)
  have hNK:N≤normalizer (K:Set G):=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hWn:W.map f≤K := by
    rintro _ ⟨_,⟨v,hv,rfl⟩,rfl⟩
    have hvf:f v∈K:=hcore (hVn ▸ mem_map_of_mem f hv)
    have hh: f g*f v*(f g)⁻¹∈K:=(mem_normalizer_iff.mp (hNK hfg) _).mp hvf
    change f (g*v*g⁻¹)∈K
    simpa only [map_mul,map_inv] using hh
  have hpair:I.map f≤K := by
    rw [map_sup,hVn]
    exact sup_le hcore hWn
  exact ((isPGroup_pCoreIn 2 N).to_le hpair).of_equiv
    (I.equivMapOfInjective f (MulAut.conj n).injective).symm


theorem internal_pair_inverse_eq (V:Subgroup G) (g:G)
    (hg:g∈V⊔V.map (MulAut.conj g).toMonoidHom) :
    V⊔V.map (MulAut.conj g⁻¹).toMonoidHom=V⊔V.map (MulAut.conj g).toMonoidHom := by
  let I:=V⊔V.map (MulAut.conj g).toMonoidHom
  have hm:I.map (MulAut.conj g⁻¹).toMonoidHom=I :=
    mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer (I.inv_mem hg))
  have hc:(V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom=V := by
    rw [map_map]
    have he:(MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom=MonoidHom.id G := by
      ext x;simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  rw [show I=V⊔V.map (MulAut.conj g).toMonoidHom from rfl,map_sup,hc,sup_comm] at hm
  exact hm
end Subgroup
