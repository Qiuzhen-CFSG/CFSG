module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source
public import Theory.Frattini.SquareImage
/-!
# Square actions exclude the original intrinsic pair

A square-one image kills the normalizer Frattini subgroup. The literal
commutator identity in PairAction then makes its noncyclic complement trivial.
The second theorem transports a pointwise square bound through the marked
normal component, preserving the actual ambient normalizer and conjugation.
Source: the nondefining odd degree-three cases in Aschbacher–Smith 1.3.4,
printed pp.510–511, using the intrinsic Frattini commutator hypothesis.
-/
public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
variable {J H : Type*} [Group J] [Finite J] [Group H]
variable {κ : GroupClass} {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}

theorem false_of_square_normalizer_action [Fact p.Prime]
    (ha : SourceTransport.PairAction p (S : Subgroup J) B)
    (hs : ∀s:(S ⊓ normalizer B : Subgroup J),
      (B.normalizerMonoidHom (inclusion inf_le_right s))^2=1) : False := by
  let N := (S : Subgroup J) ⊓ normalizer B
  let f := B.normalizerMonoidHom.comp (inclusion (show N≤normalizer B from inf_le_right))
  have hk := Theory.GroupTheory.frattini_le_ker_of_square_image f hs
  have hc : (frattini N).map N.subtype≤centralizer (B:Set J) := by
    rintro x ⟨s,hs,rfl⟩
    have he : f s=1 := hk hs
    intro b hb
    have hh := congrArg (fun z : MulAut B => (z ⟨b,hb⟩ : J)) he
    change (s:J)*b*(s:J)⁻¹=b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hbot : B=⊥ := by
    rw [ha.commutator,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hcyc : IsCyclic B := by rw [hbot];infer_instance
  exact ha.oddComplement.not_isCyclic hcyc

/-- A pointwise square-one theorem for the actual marked component kills the
original Frattini commutator action. -/
theorem false_of_component_square
    (h : OddCartan.AmbientInput κ D B S p)
    (ha : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D≃*H)
    (hs : ∀P:Subgroup H,IsPGroup p P→∀β:MulAut H,
      (∃n:ℕ,β^(2^n)=1)→(∀x,β x∈P↔x∈P)→∀b∈P,β (β b)=b) : False := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  let _ : D.Normal := h.normal
  let N := (S : Subgroup J)⊓normalizer B
  let P := (B.subgroupOf D).map e.toMonoidHom
  have hP : IsPGroup p P := h.p_group.comap_subtype.map e.toMonoidHom
  let f : N→*MulAut H := (MulAut.congr e).toMonoidHom.comp
    ((MulAut.conjNormal : J→*MulAut D).comp N.subtype)
  have hN : IsPGroup 2 N := S.isPGroup'.to_le inf_le_left
  have hmem (y:H) : y∈P↔(e.symm y).val∈B := by
    constructor
    · rintro ⟨x,hx,rfl⟩
      change x.val∈B at hx
      simpa only [MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using hx
    · intro hy
      exact ⟨e.symm y,hy,e.apply_symm_apply y⟩
  apply false_of_square_normalizer_action ha
  intro s
  have hf : ∃n:ℕ,(f s)^(2^n)=1 := by
    obtain ⟨n,hn⟩ := hN s
    exact ⟨n,by rw [← map_pow,hn,map_one]⟩
  have hstable : ∀y,f s y∈P↔y∈P := by
    intro y
    rw [hmem,hmem]
    change (e.symm (e (MulAut.conjNormal (s:J) (e.symm y)))).val∈B↔_
    rw [e.symm_apply_apply,MulAut.conjNormal_apply]
    exact (mem_normalizer_iff.mp s.property.2 _).symm
  have hs' := hs P hP (f s) hf hstable
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  let bD : D := ⟨b.val,h.inside b.property⟩
  have hbD : e bD∈P := mem_map_of_mem e.toMonoidHom b.property
  have he := hs' (e bD) hbD
  have hfe (x:D) : f s (e x)=e (MulAut.conjNormal (s:J) x) := by
    change e (MulAut.conjNormal (s:J) (e.symm (e x)))=_
    rw [e.symm_apply_apply]
  rw [hfe,hfe] at he
  change (s:J)*((s:J)*b.val*(s:J)⁻¹)*(s:J)⁻¹=b.val
  exact congrArg (fun x:D=>x.val) (e.injective he)
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.OddSource
