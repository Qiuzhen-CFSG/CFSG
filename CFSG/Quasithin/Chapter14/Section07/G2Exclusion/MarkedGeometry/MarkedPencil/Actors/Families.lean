module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors

/-!
# The binary G₂ pencil commutator families

At the first singular point the full pencil centralizer consists of
`rootActor a b c`, and its intersection with the actual derived group consists
of `rootActor a b 0`. For a trace-zero vector `w` with seventh coordinate zero,
the displacement of an arbitrary vector `v` by `rootActor (w 5) (w 6) 0`
equals the displacement of `w` by `rootActor (v 5) (v 6) (v 7)`.
Conversely, every three root parameters occur as these coordinates of a
trace-zero vector. Taking spans proves the commutator equality, including
zero vectors and the identity actor.

Equivariant linear images pass this calculation to the genuine natural
quotient; point transitivity and preservation of the polar form pass it to
every singular point in both models. The elementary eight remains in the
full G₂(2) actor throughout.

These are the concrete model equalities used in Aschbacher–Smith 14.7.55(8),
combined manuscript of 1 March 2004, printed p.1066, PDF p.1083. Here `W` is
the marked perpendicular. Its identification with the span of fixed spaces
and the literal source-quotient application belong to the assembling branch.
Root conventions come from the existing licensed ATLAS port; see
LICENSES/ATLAS.txt. No additional ATLAS source is copied here.
-/

@[expose] public noncomputable section

open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural Atlas.G2.Explicit
open Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors.Families

private theorem pair_displacement (w v : TraceZero (ZMod 2)) (hw : w.val 7 = 0) :
    traceZeroAction (ZMod 2) (rootActor (w.val 5) (w.val 6) 0) v - v =
      traceZeroAction (ZMod 2) (rootActor (v.val 5) (v.val 6) (v.val 7)) w - w := by
  apply Subtype.ext
  simp only [Submodule.coe_sub, traceZeroAction_val, rootActor_apply]
  have ht : w.val 3 + w.val 4 = 0 := w.property
  ext i
  fin_cases i <;> simp [Pi.sub_apply, hw, ht] <;> ring

private def upper (a b c : ZMod 2) : TraceZero (ZMod 2) :=
  ⟨![0,0,0,0,0,a,b,c], by simp [trace]⟩

private theorem root_mem_elementary (a b c : ZMod 2) :
    rootActor a b c ∈ BinaryCore.elementary :=
  ⟨⟨a,b,c,0,0⟩, ⟨rfl,rfl⟩,rfl⟩

private theorem root_mem_natural (a b : ZMod 2) :
    rootActor a b 0 ∈ BinaryCore.natural :=
  ⟨⟨a,b,0,0,0⟩, ⟨rfl,rfl,rfl⟩,rfl⟩

private theorem elementary_exists (g : Model (ZMod 2)) (hg : g ∈ BinaryCore.elementary) :
    ∃ a b c, g = rootActor a b c := by
  obtain ⟨x,⟨hd,he⟩,rfl⟩ := hg
  have hx : x = ⟨x.a,x.b,x.c,0,0⟩ := by cases x; simp_all
  exact ⟨x.a,x.b,x.c,congrArg BinaryCore.embedding hx⟩

private theorem natural_exists (g : Model (ZMod 2)) (hg : g ∈ BinaryCore.natural) :
    ∃ a b, g = rootActor a b 0 := by
  obtain ⟨x,⟨hc,hd,he⟩,rfl⟩ := hg
  have hx : x = ⟨x.a,x.b,0,0,0⟩ := by cases x; simp_all
  exact ⟨x.a,x.b,congrArg BinaryCore.embedding hx⟩


private theorem commutator_transport {G D V W : Type*} [Group G] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G V) (ρ : Representation (ZMod 2) D W)
    (e : V →ₗ[ZMod 2] W) (α : G →* D)
    (he : ∀ g v, ρ (α g) (e v) = e (σ g v))
    (P : Submodule (ZMod 2) V) (A : Subgroup G) :
    subspaceCommutator ρ (P.map e) (A.map α) =
      (subspaceCommutator σ P A).map e := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨g,hg,rfl⟩,_,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨σ g v - v, Submodule.subset_span ⟨g,hg,v,hv,rfl⟩, ?_⟩
    rw [map_sub,he]
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    change e (σ g v - v) ∈ subspaceCommutator ρ (P.map e) (A.map α)
    rw [map_sub,← he]
    exact Submodule.subset_span ⟨α g,⟨g,hg,rfl⟩,e v,⟨v,hv,rfl⟩,rfl⟩

private theorem cyclic_le {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (b : G) (S : Submodule (ZMod 2) V)
    (h : ∀ v, ρ b v - v ∈ S) : subspaceCommutator ρ ⊤ (Subgroup.zpowers b) ≤ S := by
  have hp (n : ℕ) (v : V) : ρ (b ^ n) v - v ∈ S := by
    induction n generalizing v with
    | zero => simp
    | succ n ih =>
      have he : ρ (b ^ (n+1)) v - v =
          (ρ (b ^ n) (ρ b v) - ρ b v) + (ρ b v - v) := by
        rw [pow_succ,map_mul,Module.End.mul_apply]
        abel
      rw [he]
      exact S.add_mem (ih _) (h v)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,v,_,rfl⟩
  obtain ⟨n,rfl⟩ := (Submonoid.mem_powers_iff a b).mp (mem_powers_iff_mem_zpowers.mpr ha)
  exact hp n v

private theorem weyl_match (w : TraceZero (ZMod 2)) (hw : w.val 7 = 0) :
    subspaceCommutator (traceZeroAction (ZMod 2)) ⊤
        (Subgroup.zpowers (rootActor (w.val 5) (w.val 6) 0)) =
      subspaceCommutator (traceZeroAction (ZMod 2)) ((ZMod 2) ∙ w) BinaryCore.elementary := by
  apply le_antisymm
  · apply cyclic_le
    intro v
    rw [pair_displacement w v hw]
    exact Submodule.subset_span ⟨_,root_mem_elementary _ _ _,w,
      Submodule.mem_span_singleton_self w,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,y,hy,rfl⟩
    obtain ⟨a,b,c,rfl⟩ := elementary_exists g hg
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [(traceZeroAction (ZMod 2) (rootActor a b c)).map_smul r w]
    rw [← smul_sub (M := ZMod 2)]
    apply Submodule.smul_mem
    have he := pair_displacement w (upper a b c) hw
    change _ = traceZeroAction (ZMod 2) (rootActor a b c) w - w at he
    rw [← he]
    exact Submodule.subset_span ⟨_,Subgroup.mem_zpowers _,upper a b c,Submodule.mem_top,rfl⟩

private theorem binary_rep_mk (v : Carrier (ZMod 2)) (hv : v ≠ 0) :
    (Projectivization.mk (ZMod 2) v hv).rep = v := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod 2) v hv
  have hb : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  have h1 : (a : ZMod 2) = 1 := (hb a).resolve_left a.ne_zero
  simpa only [Units.smul_def,h1,one_smul] using ha.symm

private theorem first_rep : (firstPoint (K := ZMod 2)).val.rep = basisVector 0 := by
  exact binary_rep_mk _ _

private theorem smul_rep (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    (g • p).val.rep = g.val p.val.rep := by
  conv_lhs => rw [← singularPointMk_rep (ZMod 2) p,singularPointMk_smul]
  exact binary_rep_mk _ _

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
private theorem perpendicular_first (f : SingularMap W) (w : W) :
    w ∈ perpendicular f firstPoint ↔ ∃ v : TraceZero (ZMod 2), v.val 7 = 0 ∧ f.linear v = w := by
  change (∃ v : TraceZero (ZMod 2), v.val ∈ LinearMap.ker (normPolar firstPoint.val.rep) ∧
    f.linear v = w) ↔ _
  simp [first_rep, normPolar, basisVector, LinearMap.mem_ker]

private theorem perpendicular_transport (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    (perpendicular f p).map (ρ g) = perpendicular f (g • p) := by
  ext y
  constructor
  · rintro ⟨_,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨traceZeroAction (ZMod 2) g v, ?_, (hf g v).symm⟩
    change normPolar (g • p).val.rep (g.val v.val) = 0
    rw [smul_rep,automorphism_normPolar]
    exact hv
  · rintro ⟨v,hv,rfl⟩
    refine ⟨f.linear (traceZeroAction (ZMod 2) g⁻¹ v), ?_, ?_⟩
    · refine ⟨traceZeroAction (ZMod 2) g⁻¹ v, ?_,rfl⟩
      change normPolar p.val.rep (g⁻¹.val v.val) = 0
      have he := automorphism_normPolar g p.val.rep (g⁻¹.val v.val)
      have hi : g.val (g⁻¹.val v.val) = v.val := by
        exact congrArg Subtype.val ((traceZeroAction (ZMod 2)).self_inv_apply g v)
      rw [hi, ← smul_rep] at he
      exact he.symm.trans hv
    · rw [hf, (traceZeroAction (ZMod 2)).self_inv_apply]

private theorem image_commutator (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (P : Submodule (ZMod 2) (TraceZero (ZMod 2))) (A : Subgroup (Model (ZMod 2))) :
    subspaceCommutator ρ (P.map f.linear) A =
      (subspaceCommutator (traceZeroAction (ZMod 2)) P A).map f.linear := by
  simpa only [Subgroup.map_id] using commutator_transport
    (traceZeroAction (ZMod 2)) ρ f.linear (MonoidHom.id _) hf P A

private theorem image_match (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (hs : Function.Surjective f.linear) (w : TraceZero (ZMod 2)) (hw : w.val 7 = 0) :
    subspaceCommutator ρ ⊤ (Subgroup.zpowers (rootActor (w.val 5) (w.val 6) 0)) =
      subspaceCommutator ρ ((ZMod 2) ∙ f.linear w) BinaryCore.elementary := by
  have h := congrArg (Submodule.map f.linear) (weyl_match w hw)
  rw [← image_commutator f ρ hf, ← image_commutator f ρ hf,
    Submodule.map_top, LinearMap.range_eq_top.mpr hs,
    Submodule.map_span, Set.image_singleton] at h
  exact h

private theorem first_families (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (hs : Function.Surjective f.linear) :
    {S | ∃ b ∈ derivedCentralizer f ρ firstPoint,
      S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} =
    {S | ∃ w ∈ perpendicular f firstPoint,
      S = subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ firstPoint)} := by
  rw [derivedCentralizer_firstPoint f ρ hf,fullCentralizer_firstPoint f ρ hf]
  ext S
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨a,b,rfl⟩ := natural_exists b hb
    refine ⟨f.linear (upper a b 0), (perpendicular_first f _).mpr ⟨upper a b 0,rfl,rfl⟩, ?_⟩
    exact image_match f ρ hf hs (upper a b 0) rfl
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨v,hv,rfl⟩ := (perpendicular_first f w).mp hw
    exact ⟨rootActor (v.val 5) (v.val 6) 0,root_mem_natural _ _,
      (image_match f ρ hf hs v hv).symm⟩

private theorem commutator_conjugate
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (g : Model (ZMod 2)) (P : Submodule (ZMod 2) W) (A : Subgroup (Model (ZMod 2))) :
    subspaceCommutator ρ (P.map (ρ g)) (A.map (MulAut.conj g).toMonoidHom) =
      (subspaceCommutator ρ P A).map (ρ g) := by
  apply commutator_transport
  intro a v
  change ρ (g*a*g⁻¹) (ρ g v) = ρ g (ρ a v)
  simp only [map_mul,Module.End.mul_apply,ρ.inv_self_apply]

private theorem commutator_conjugate_top
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (g b : Model (ZMod 2)) :
    subspaceCommutator ρ ⊤ (Subgroup.zpowers ((MulAut.conj g).toMonoidHom b)) =
      (subspaceCommutator ρ ⊤ (Subgroup.zpowers b)).map (ρ g) := by
  have ht : (⊤ : Submodule (ZMod 2) W).map (ρ g) = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (fun w => ⟨ρ g⁻¹ w,ρ.self_inv_apply g w⟩)
  simpa only [ht,MonoidHom.map_zpowers] using
    commutator_conjugate ρ g ⊤ (Subgroup.zpowers b)

private theorem commutator_conjugate_line (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) (w : W) :
    subspaceCommutator ρ ((ZMod 2) ∙ ρ g w) (fullCentralizer f ρ (g • p)) =
      (subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ p)).map (ρ g) := by
  simpa only [Submodule.map_span,Set.image_singleton,fullCentralizer_conjugate f ρ hf] using
    commutator_conjugate ρ g ((ZMod 2) ∙ w) (fullCentralizer f ρ p)

private theorem families_conjugate (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2))
    (hp : {S | ∃ b ∈ derivedCentralizer f ρ p,
      S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} =
      {S | ∃ w ∈ perpendicular f p,
      S = subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ p)}) :
    {S | ∃ b ∈ derivedCentralizer f ρ (g • p),
      S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} =
    {S | ∃ w ∈ perpendicular f (g • p),
      S = subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ (g • p))} := by
  have left : {S | ∃ b ∈ derivedCentralizer f ρ (g • p),
      S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} =
      (fun S => S.map (ρ g)) '' {S | ∃ b ∈ derivedCentralizer f ρ p,
      S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} := by
    rw [← derivedCentralizer_conjugate f ρ hf]
    ext S
    constructor
    · rintro ⟨_,⟨b,hb,rfl⟩,rfl⟩
      exact ⟨_,⟨b,hb,rfl⟩,(commutator_conjugate_top ρ g b).symm⟩
    · rintro ⟨_,⟨b,hb,rfl⟩,rfl⟩
      exact ⟨_,⟨b,hb,rfl⟩,(commutator_conjugate_top ρ g b).symm⟩
  have right : {S | ∃ w ∈ perpendicular f (g • p),
      S = subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ (g • p))} =
      (fun S => S.map (ρ g)) '' {S | ∃ w ∈ perpendicular f p,
      S = subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ p)} := by
    rw [← perpendicular_transport f ρ hf]
    ext S
    constructor
    · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
      exact ⟨_,⟨w,hw,rfl⟩,(commutator_conjugate_line f ρ hf g p w).symm⟩
    · rintro ⟨_,⟨w,hw,rfl⟩,rfl⟩
      exact ⟨_,⟨w,hw,rfl⟩,(commutator_conjugate_line f ρ hf g p w).symm⟩
  rw [left,right,hp]

private theorem all_families (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (hs : Function.Surjective f.linear) (p : SingularPoints (ZMod 2)) :
    {S | ∃ b ∈ derivedCentralizer f ρ p,
      S = subspaceCommutator ρ ⊤ (Subgroup.zpowers b)} =
    {S | ∃ w ∈ perpendicular f p,
      S = subspaceCommutator ρ ((ZMod 2) ∙ w) (fullCentralizer f ρ p)} := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg,inv_smul_smul]
  rw [← hp]
  exact families_conjugate f ρ hf g⁻¹ firstPoint (first_families f ρ hf hs)

/-- The commutator families in the actual natural quotient, including the zero subspace. -/
theorem natural_commutator_families (p : SingularPoints (ZMod 2)) :
    {S | ∃ b ∈ derivedCentralizer naturalMap (action (ZMod 2)) p,
      S = subspaceCommutator (action (ZMod 2)) ⊤ (Subgroup.zpowers b)} =
    {S | ∃ w ∈ perpendicular naturalMap p,
      S = subspaceCommutator (action (ZMod 2)) ((ZMod 2) ∙ w)
        (fullCentralizer naturalMap (action (ZMod 2)) p)} :=
  all_families naturalMap (action (ZMod 2)) naturalMap_equivariant (mk_surjective (ZMod 2)) p

/-- The commutator families in the actual trace-zero Weyl module, including the zero subspace. -/
theorem weyl_commutator_families (p : SingularPoints (ZMod 2)) :
    {S | ∃ b ∈ derivedCentralizer weylMap (traceZeroAction (ZMod 2)) p,
      S = subspaceCommutator (traceZeroAction (ZMod 2)) ⊤ (Subgroup.zpowers b)} =
    {S | ∃ w ∈ perpendicular weylMap p,
      S = subspaceCommutator (traceZeroAction (ZMod 2)) ((ZMod 2) ∙ w)
        (fullCentralizer weylMap (traceZeroAction (ZMod 2)) p)} :=
  all_families weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant (fun w => ⟨w,rfl⟩) p


end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors.Families
