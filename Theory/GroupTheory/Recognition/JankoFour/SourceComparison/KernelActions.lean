module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Residual
/-!
# Agreement of the full plane--line actions on K

Restrict the point isomorphism to the literal line kernel and compare the
two actions of H∩N_G(Z). Overlap agreement makes their discrepancy fix
K∩H pointwise. Residual identifies it with conjugation by Z(H), hence it
has exponent two and centralizes the source action. It vanishes on the
point stabilizer, of index five, so the discrepancy homomorphism is trivial.
This proves conjugation agreement for every actor in H∩N_G(Z), including
the supplied edge reversal, without choosing a new abstract involution.

Source: Aschbacher--Segev (1991), section 8, pp.606--607. The odd-index
argument accounts for the central correction in the source's final comparison.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry SourceCycleBase GraphUniquenessSystem
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
variable (a : SourceIncidence.LocalData h)
/-- The literal plane--line group normalizes the original line kernel. -/
theorem line_normalizes_kernel : a.L.G₂ ≤ normalizer (a.d.K : Set G) := by
  rw [a.line_normalizer]
  exact (normal_subgroupOf_iff_le_normalizer a.d.K_le_normalizer).mp a.d.K_normal

def planeLineKernelAction : (a.L.G₂ ⊓ centralizer z : Subgroup G) →* MulAut a.d.K :=
  a.d.K.normalizerMonoidHom.comp (inclusion (inf_le_left.trans (line_normalizes_kernel a)))

theorem planeLineKernelAction_apply (n : (a.L.G₂ ⊓ centralizer z : Subgroup G)) (k : a.d.K) :
    (planeLineKernelAction a n k : G)=(n : G)*k*(n : G)⁻¹ := rfl

private theorem central_correction_sq (c : a.d.K)
    (hc : (c : G) ∈ (center (centralizer z)).map (centralizer z).subtype) :
    (MulAut.conj c)^2=1 := by
  rw [h.centralizer_center_image] at hc
  have hc2 : c^2=1 := by
    apply Subtype.ext
    have he := pow_card_eq_one' (x := (⟨(c : G),hc⟩ : zpowers z))
    rw [Nat.card_zpowers,h.involution] at he
    change (c : G)^2=1
    exact congrArg Subtype.val he
  rw [←map_pow,hc2,map_one]

private theorem central_correction_commute (c : a.d.K)
    (hc : (c : G) ∈ (center (centralizer z)).map (centralizer z).subtype)
    (n : (a.L.G₂ ⊓ centralizer z : Subgroup G)) :
    Commute (MulAut.conj c) (planeLineKernelAction a n) := by
  obtain ⟨u,hu,he⟩ := hc
  have hnc : (n : G)*(c : G)=(c : G)*(n : G) := by
    have hh : (n : G)*(u : G)=(u : G)*(n : G) :=
      congrArg Subtype.val (mem_center_iff.mp hu (⟨n,n.property.2⟩ : centralizer z))
    change (u : G)=(c : G) at he
    rwa [he] at hh
  change MulAut.conj c*planeLineKernelAction a n=planeLineKernelAction a n*MulAut.conj c
  apply MulEquiv.ext
  intro k
  apply Subtype.ext
  change (c : G)*((n : G)*k*(n : G)⁻¹)*(c : G)⁻¹ =
    (n : G)*((c : G)*k*(c : G)⁻¹)*(n : G)⁻¹
  have heq : (c : G)*(n : G)=(n : G)*(c : G) := hnc.symm
  calc
    _ = ((c : G)*(n : G))*(k : G)*((c : G)*(n : G))⁻¹ := by group
    _ = ((n : G)*(c : G))*(k : G)*((n : G)*(c : G))⁻¹ := by rw [heq]
    _ = _ := by group

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsTypeJ4 z'}
variable (a' : SourceIncidence.LocalData h')

private noncomputable def pointKernelEquiv (φ : a.P.M ≃* a'.P.M)
    (hK : (a.d.K.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.K.subgroupOf a'.P.M) :
    a.d.K ≃* a'.d.K :=
  (subgroupOfEquivOfLe a.K_le_point).symm.trans
    (((φ.subgroupMap (a.d.K.subgroupOf a.P.M)).trans (MulEquiv.subgroupCongr hK)).trans
      (subgroupOfEquivOfLe a'.K_le_point))

private theorem pointKernelEquiv_coe (φ : a.P.M ≃* a'.P.M)
    (hK : (a.d.K.subgroupOf a.P.M).map φ.toMonoidHom=a'.d.K.subgroupOf a'.P.M)
    (k : a.d.K) :
    (pointKernelEquiv a a' φ hK k : G')=(φ ⟨k,a.K_le_point k.property⟩ : G') := rfl

private def planeLineMap (φ : centralizer z ≃* centralizer z')
    (hL : (a.L.G₂.subgroupOf (centralizer z)).map φ.toMonoidHom=
      a'.L.G₂.subgroupOf (centralizer z')) :
    (a.L.G₂ ⊓ centralizer z : Subgroup G) →* (a'.L.G₂ ⊓ centralizer z' : Subgroup G') where
  toFun n := ⟨φ ⟨n,n.property.2⟩,by
    have hm := mem_map_of_mem φ.toMonoidHom
      (show (⟨n,n.property.2⟩ : centralizer z) ∈ a.L.G₂.subgroupOf (centralizer z) from n.property.1)
    rw [hL] at hm
    exact ⟨hm,(φ ⟨n,n.property.2⟩).property⟩⟩
  map_one' := by
    apply Subtype.ext
    change (φ 1 : G')=1
    exact congrArg Subtype.val φ.map_one
  map_mul' n m := by
    apply Subtype.ext
    change (φ (⟨n,n.property.2⟩*⟨m,m.property.2⟩) : G')=_
    exact congrArg Subtype.val (φ.map_mul ⟨n,n.property.2⟩ ⟨m,m.property.2⟩)

/-- Once the local maps agree on I and retain the actual K and plane--line
flag, their conjugation actions agree on all K. The central residual is
eliminated by the odd index five of the point stabilizer. -/
theorem compatible_kernel_conjugation
    (M : a.P.M ≃* a'.P.M) (H : centralizer z ≃* centralizer z')
    (hK : (a.d.K.subgroupOf a.P.M).map M.toMonoidHom=a'.d.K.subgroupOf a'.P.M)
    (hL : (a.L.G₂.subgroupOf (centralizer z)).map H.toMonoidHom=
      a'.L.G₂.subgroupOf (centralizer z'))
    (agree : ∀ (k : G) (hkM : k ∈ a.P.M) (hkH : k ∈ centralizer z),
      (M ⟨k,hkM⟩ : G')=(H ⟨k,hkH⟩ : G'))
    (n : (a.L.G₂ ⊓ centralizer z : Subgroup G)) (k : a.d.K) :
    (M ⟨(n : G)*k*(n : G)⁻¹,a.K_le_point (planeLineKernelAction a n k).property⟩ : G') =
      (H ⟨n,n.property.2⟩ : G')*(M ⟨k,a.K_le_point k.property⟩ : G')*
        (H ⟨n,n.property.2⟩ : G')⁻¹ := by
  let e := pointKernelEquiv a a' M hK
  let f := planeLineKernelAction a
  let g := (MulAut.congr e.symm).toMonoidHom.comp
    ((planeLineKernelAction a').comp (planeLineMap a a' H hL))
  have eg (n : (a.L.G₂ ⊓ centralizer z : Subgroup G)) (k : a.d.K) :
      e (g n k)=planeLineKernelAction a' (planeLineMap a a' H hL n) (e k) := by
    change e (e.symm _)=_
    exact e.apply_symm_apply _
  have fH (n : (a.L.G₂ ⊓ centralizer z : Subgroup G)) (k : a.d.K) (hk : (k : G) ∈ centralizer z) :
      (f n k : G) ∈ centralizer z :=
    (centralizer z).mul_mem ((centralizer z).mul_mem n.property.2 hk)
      ((centralizer z).inv_mem n.property.2)
  have agreeI (n : (a.L.G₂ ⊓ centralizer z : Subgroup G)) (k : a.d.K)
      (hk : (k : G) ∈ centralizer z) : g n k=f n k := by
    apply e.injective
    rw [eg]
    apply Subtype.ext
    rw [planeLineKernelAction_apply,pointKernelEquiv_coe,pointKernelEquiv_coe]
    rw [agree _ _ hk,agree _ _ (fH n k hk)]
    change (H ⟨n,n.property.2⟩ : G')*(H ⟨k,hk⟩ : G')*(H ⟨n,n.property.2⟩ : G')⁻¹ =
      (H (⟨n,n.property.2⟩*⟨k,hk⟩*(⟨n,n.property.2⟩ : centralizer z)⁻¹) : G')
    simp only [map_mul,map_inv,coe_mul,coe_inv]
  have residual (n : (a.L.G₂ ⊓ centralizer z : Subgroup G)) :
      ∃ c : a.d.K, (c : G) ∈ (center (centralizer z)).map (centralizer z).subtype ∧
        g n*(f n)⁻¹=MulAut.conj c := by
    apply lineKernel_residual_inner a
    intro k
    change g n ((f n)⁻¹ k)=k
    have hi : (f n)⁻¹ k=f n⁻¹ k := by rw [map_inv]
    rw [hi,agreeI n (f n⁻¹ k) (fH n⁻¹ k k.property)]
    exact (f n).apply_symm_apply k
  let I := a.P.M.subgroupOf (a.L.G₂ ⊓ centralizer z)
  have hI : Odd I.index := by
    have hi := a.triple_indices.2
    rw [inf_assoc,inf_relIndex_right] at hi
    change a.P.M.relIndex (a.L.G₂ ⊓ centralizer z)=5 at hi
    change Odd (a.P.M.relIndex (a.L.G₂ ⊓ centralizer z))
    rw [hi]
    decide
  have hfg : f=g := hom_eq_of_odd_index_of_central_discrepancy I hI f g
    (by
      intro i
      apply MulEquiv.ext
      intro k
      apply e.injective
      rw [eg]
      apply Subtype.ext
      rw [planeLineKernelAction_apply,pointKernelEquiv_coe,pointKernelEquiv_coe]
      have hi := agree (i.val : G) i.property i.val.property.2
      change (M ((⟨i.val,i.property⟩ : a.P.M)*⟨k,a.K_le_point k.property⟩*
        (⟨i.val,i.property⟩ : a.P.M)⁻¹) : G')=_
      simp only [map_mul,map_inv,coe_mul,coe_inv]
      rw [hi]
      rfl)
    (by intro n m; obtain ⟨c,hc,he⟩ := residual n; rw [he]; exact central_correction_commute a c hc m)
    (by intro n; obtain ⟨c,hc,he⟩ := residual n; rw [he]; exact central_correction_sq a c hc)
  have he := congrArg (fun q : a.d.K => (e q : G'))
    (congrArg (fun u : (a.L.G₂ ⊓ centralizer z : Subgroup G) →* MulAut a.d.K => u n k) hfg)
  rw [eg] at he
  exact he


end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
