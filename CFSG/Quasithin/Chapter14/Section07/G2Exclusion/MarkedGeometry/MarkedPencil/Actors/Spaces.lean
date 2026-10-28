module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors
public import Theory.Representation.BinaryOffender.FixedSpaceSpan
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.ConjugationTools

/-!
# Fixed and moved spaces of the binary G₂ pencil centralizers

At the first singular point, the nontrivial roots `(a,b,0)` move the actual
zero-product plane spanned by `e₀` and `a e₁ + b e₂`. Their fixed spaces span
the polar hyperplane `x₇ = 0`. The common fixed space of the root four is
`x₅ = x₆ = x₇ = 0`; it is also the fixed space of every root `(a,b,1)` and
the moved space of the root eight. This space includes the scalar identity
line in the Weyl module, so the pencil span must be joined with the full
actor's fixed space.

Point transitivity and conjugation give these identities at every singular
point. The natural model is the genuine quotient by the scalar identity
line. Norm preservation shows that fixation in this quotient reflects
fixation of trace-zero representatives, allowing the fixed-space identities
to descend along with the moved spaces. The perpendicular quotient has
rank one in both models.

These are the fixed/moved-space assertions of Aschbacher–Smith 14.7.55(4),
combined manuscript of 1 March 2004, printed p.1066, PDF p.1083. The source
assembly and transport to its literal group quotient belong to the parent
pencil-centralizer development. The existing octonion and root conventions
come from the attributed ATLAS port; see LICENSES/ATLAS.txt. No additional
ATLAS source is copied here.
-/

@[expose] public noncomputable section
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural Atlas.G2.Explicit
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors
local notation "T" => TraceZero (ZMod 2)
local notation "σ" => traceZeroAction (ZMod 2)
private def vec (a b c d e f g : ZMod 2) : T :=
  ⟨![a,b,c,d,d,e,f,g], by simp [mem_traceZero, trace, CharTwo.add_self_eq_zero]⟩
private theorem trace_coords (x : T) : x.val 4 = x.val 3 := by
  have h : x.val 3 + x.val 4 = 0 := x.property
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h
private theorem root_fix (a b c : ZMod 2) (x : T) :
    σ (rootActor a b c) x = x ↔
      a*x.val 6+b*x.val 5+c*x.val 7=0 ∧
      c*x.val 5+a*x.val 7=0 ∧ c*x.val 6+b*x.val 7=0 ∧ c*x.val 7=0 := by
  rw [Subtype.ext_iff]
  change (rootActor a b c).val x.val = x.val ↔ _
  rw [rootActor_apply, funext_iff]
  simp [Fin.forall_fin_succ, trace_coords x, CharTwo.add_self_eq_zero, add_assoc]
private theorem root_zero : rootActor 0 0 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  ext x i
  fin_cases i <;> simp [rootActor_apply]
private theorem root_ne (a b : ZMod 2) (h : a ≠ 0 ∨ b ≠ 0) : rootActor a b 0 ≠ 1 := by
  intro he
  have hh := rootActor_apply a b 0 (basisVector 7)
  rw [he] at hh
  have h1 := congrFun hh 1
  have h2 := congrFun hh 2
  simp [basisVector] at h1 h2
  rcases h with h | h
  · exact h h1.symm
  · exact h h2.symm
private theorem elementary_roots (g : Model (ZMod 2)) :
    g ∈ BinaryCore.elementary ↔ ∃ a b c, g = rootActor a b c := by
  constructor
  · rintro ⟨x,⟨hd,he⟩,rfl⟩
    refine ⟨x.a,x.b,x.c,?_⟩
    congr 1
    cases x
    simp_all
  · rintro ⟨a,b,c,rfl⟩
    exact ⟨⟨a,b,c,0,0⟩,⟨rfl,rfl⟩,rfl⟩
private theorem natural_roots (g : Model (ZMod 2)) :
    g ∈ BinaryCore.natural ↔ ∃ a b, g = rootActor a b 0 := by
  rw [← elementary_inf_derived]
  constructor
  · rintro ⟨hg,hd⟩
    obtain ⟨a,b,c,rfl⟩ := (elementary_roots g).mp hg
    exact ⟨a,b,by rw [(rootActor_mem_derived a b c).mp hd]⟩
  · rintro ⟨a,b,rfl⟩
    exact ⟨(elementary_roots _).mpr ⟨a,b,0,rfl⟩,(rootActor_mem_derived a b 0).mpr rfl⟩
private def baseFixed : Submodule (ZMod 2) T where
  carrier := {x | x.val 5 = 0 ∧ x.val 6 = 0 ∧ x.val 7 = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨h5,h6,h7⟩ ⟨k5,k6,k7⟩; simp_all
  smul_mem' := by rintro a x ⟨h5,h6,h7⟩; simp_all
private def lastCoord : T →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj 7).comp (TraceZero (ZMod 2)).subtype
private abbrev baseHyperplane := LinearMap.ker lastCoord
private theorem base_fixed : fixedSpace σ BinaryCore.natural = baseFixed := by
  ext x
  constructor
  · intro hx
    have hA := (root_fix 1 0 0 x).mp (hx ⟨rootActor 1 0 0,
      (natural_roots _).mpr ⟨1,0,rfl⟩⟩)
    have hB := (root_fix 0 1 0 x).mp (hx ⟨rootActor 0 1 0,
      (natural_roots _).mpr ⟨0,1,rfl⟩⟩)
    simpa [baseFixed] using And.intro hB.1 (And.intro hA.1 hA.2.1)
  · intro hx ⟨g,hg⟩
    obtain ⟨a,b,rfl⟩ := (natural_roots g).mp hg
    apply (root_fix a b 0 x).mpr
    rcases hx with ⟨h5,h6,h7⟩
    simp [h5,h6,h7]
private theorem outer_fixed (a b : ZMod 2) :
    fixedSpace σ (Subgroup.zpowers (rootActor a b 1)) = baseFixed := by
  ext x
  rw [mem_fixedSpace_zpowers_iff, root_fix]
  change _ ↔ x.val 5=0 ∧ x.val 6=0 ∧ x.val 7=0
  constructor
  · rintro ⟨h0,h1,h2,h7⟩
    simp only [one_mul] at h0 h1 h2 h7
    exact ⟨by simpa [h7] using h1,by simpa [h7] using h2,h7⟩
  · rintro ⟨h5,h6,h7⟩
    simp [h5,h6,h7]
private theorem base_fixedSpan : fixedSpaceSpan σ BinaryCore.natural = baseHyperplane := by
  apply le_antisymm
  · apply fixedSpaceSpan_le
    intro g hg hn x hx
    obtain ⟨a,b,rfl⟩ := (natural_roots g).mp hg
    have h := (root_fix a b 0 x).mp ((mem_fixedSpace_zpowers_iff _ _ _).mp hx)
    change x.val 7 = 0
    by_cases ha : a=0
    · have hb : b ≠ 0 := by intro hb; subst a; subst b; exact hn root_zero
      exact (mul_eq_zero.mp (by simpa using h.2.2.1)).resolve_left hb
    · exact (mul_eq_zero.mp (by simpa using h.2.1)).resolve_left ha
  · intro x hx
    change x.val 7=0 at hx
    let y := vec 0 0 0 0 0 (x.val 6) 0
    have hy : y ∈ fixedSpace σ (Subgroup.zpowers (rootActor 0 1 0)) := by
      rw [mem_fixedSpace_zpowers_iff,root_fix]
      simp [y,vec]
    have hz : x-y ∈ fixedSpace σ (Subgroup.zpowers (rootActor 1 0 0)) := by
      rw [mem_fixedSpace_zpowers_iff,root_fix]
      simp [y,vec,hx]
    have hy' := fixedSpace_le_fixedSpaceSpan σ
      ((natural_roots _).mpr ⟨0,1,rfl⟩) (root_ne 0 1 (by simp)) hy
    have hz' := fixedSpace_le_fixedSpaceSpan σ
      ((natural_roots _).mpr ⟨1,0,rfl⟩) (root_ne 1 0 (by simp)) hz
    simpa only [sub_add_cancel] using (fixedSpaceSpan σ BinaryCore.natural).add_mem hz' hy'
private theorem weyl_image (P : Submodule (ZMod 2) (Carrier (ZMod 2))) :
    weylMap.image P = traceRestriction P := by
  simp [SingularMap.image,weylMap]
private theorem base_pencil_fixed :
    pencilSpan weylMap firstPoint ⊔ fixedSpace σ ⊤ = baseFixed := by
  rw [pencilSpan_firstPoint, weyl_image]
  apply le_antisymm
  · apply sup_le
    · intro x hx
      exact ⟨hx 5 (by decide),hx 6 (by decide),hx 7 (by decide)⟩
    · rw [← base_fixed]
      intro x hx g
      exact hx ⟨g.val,Subgroup.mem_top _⟩
  · intro x hx
    rcases hx with ⟨h5,h6,h7⟩
    let y := vec (x.val 0) (x.val 1) (x.val 2) 0 0 0 0
    have hy : y ∈ traceRestriction distinguishedPlane := by
      intro i hi
      fin_cases i <;> simp_all [y,vec]
    have hid : identity (ZMod 2) ∈ fixedSpace σ ⊤ := by
      intro g
      exact traceZeroAction_identity _ g.val
    have he : x = y + x.val 3 • identity (ZMod 2) := by
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [y,vec,identity,unit,trace_coords x,h5,h6,h7]
    rw [he]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hy)
      (Submodule.mem_sup_right ((fixedSpace σ ⊤).smul_mem _ hid))
private theorem root_diff (a b c : ZMod 2) (x : T) :
    σ (rootActor a b c) x - x =
      vec (a*x.val 6+b*x.val 5+c*x.val 7)
        (c*x.val 5+a*x.val 7) (c*x.val 6+b*x.val 7) (c*x.val 7) 0 0 0 := by
  apply Subtype.ext
  change (rootActor a b c).val x.val - x.val = _
  rw [rootActor_apply]
  ext i
  fin_cases i <;> simp [vec,trace_coords x,CharTwo.add_self_eq_zero,add_assoc]
private theorem moved_mem (g : Model (ZMod 2)) (hg : g ∈ BinaryCore.elementary) (x : T) :
    σ g x - x ∈ subspaceCommutator σ ⊤ BinaryCore.elementary :=
  Submodule.subset_span ⟨g,hg,x,Submodule.mem_top,rfl⟩
private theorem base_moved : subspaceCommutator σ ⊤ BinaryCore.elementary = baseFixed := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,x,_,rfl⟩
    obtain ⟨a,b,c,rfl⟩ := (elementary_roots g).mp hg
    rw [root_diff]
    exact ⟨rfl,rfl,rfl⟩
  · let M := subspaceCommutator σ ⊤ BinaryCore.elementary
    have he (a b c : ZMod 2) : rootActor a b c ∈ BinaryCore.elementary :=
      (elementary_roots _).mpr ⟨a,b,c,rfl⟩
    have h0 : vec 1 0 0 0 0 0 0 ∈ M := by
      simpa [root_diff,vec] using moved_mem _ (he 1 0 0) (vec 0 0 0 0 0 1 0)
    have h1 : vec 0 1 0 0 0 0 0 ∈ M := by
      simpa [root_diff,vec] using moved_mem _ (he 1 0 0) (vec 0 0 0 0 0 0 1)
    have h2 : vec 0 0 1 0 0 0 0 ∈ M := by
      simpa [root_diff,vec] using moved_mem _ (he 0 1 0) (vec 0 0 0 0 0 0 1)
    have hd : vec 1 0 0 1 0 0 0 ∈ M := by
      simpa [root_diff,vec] using moved_mem _ (he 0 0 1) (vec 0 0 0 0 0 0 1)
    have h3 : vec 0 0 0 1 0 0 0 ∈ M := by
      have hh := M.sub_mem hd h0
      convert hh using 1
      ext i
      fin_cases i <;> simp [vec]
    intro x hx
    rcases hx with ⟨h5,h6,h7⟩
    have heq : x = x.val 0 • vec 1 0 0 0 0 0 0 + x.val 1 • vec 0 1 0 0 0 0 0 +
        x.val 2 • vec 0 0 1 0 0 0 0 + x.val 3 • vec 0 0 0 1 0 0 0 := by
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [vec,trace_coords x,h5,h6,h7]
    rw [heq]
    exact M.add_mem (M.add_mem (M.add_mem (M.smul_mem _ h0) (M.smul_mem _ h1))
      (M.smul_mem _ h2)) (M.smul_mem _ h3)
private theorem binary_rep (x : Carrier (ZMod 2)) (hx : x ≠ 0) :
    (Projectivization.mk (ZMod 2) x hx).rep = x := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod 2) x hx
  have h1 : ∀ a : (ZMod 2)ˣ, a = 1 := by decide
  simpa only [h1 a,one_smul] using ha.symm
private theorem first_rep : (firstPoint (K := ZMod 2)).val.rep = basisVector 0 :=
  binary_rep _ _
private theorem smul_rep (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    (g • p).val.rep = g.val p.val.rep := by
  conv_lhs => rw [← singularPointMk_rep (ZMod 2) p, singularPointMk_smul]
  exact binary_rep _ _
private theorem base_perp : perpendicular weylMap firstPoint = baseHyperplane := by
  rw [perpendicular,weyl_image,first_rep]
  ext x
  simp [traceRestriction,baseHyperplane,lastCoord,normPolar,basisVector]
private theorem base_codim : Module.finrank (ZMod 2) (T ⧸ baseHyperplane) = 1 := by
  have hs : Function.Surjective lastCoord := fun a => ⟨vec 0 0 0 0 0 0 a,rfl⟩
  rw [(lastCoord.quotKerEquivOfSurjective hs).finrank_eq]
  simp
private theorem cyclic_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) V) (g : Model (ZMod 2))
    (P : Submodule (ZMod 2) V) (h : ∀ x, ρ g x-x ∈ P) :
    subspaceCommutator ρ ⊤ (Subgroup.zpowers g) ≤ P := by
  have hp (n : ℕ) : ∀ x, ρ (g^n) x-x ∈ P := by
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      have he : ρ (g^(n+1)) x-x = (ρ (g^n) (ρ g x)-ρ g x)+(ρ g x-x) := by
        rw [pow_succ,map_mul,Module.End.mul_apply]
        abel
      rw [he]
      exact P.add_mem (ih _) (h x)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,x,_,rfl⟩
  obtain ⟨n,rfl⟩ := (Submonoid.mem_powers_iff a g).mp (mem_powers_iff_mem_zpowers.mpr ha)
  exact hp n x
private def rootPlane (a b : ZMod 2) : Submodule (ZMod 2) (Carrier (ZMod 2)) :=
  Submodule.span (ZMod 2) {basisVector 0,(vec 0 a b 0 0 0 0).val}
private theorem rootPlane_line (a b : ZMod 2) (hab : a ≠ 0 ∨ b ≠ 0) :
    IsZeroProductLine (rootPlane a b) := by
  constructor
  · have hn : (vec 0 a b 0 0 0 0).val ≠ 0 := by
      intro h
      have h1 := congrFun h 1
      have h2 := congrFun h 2
      simp [vec] at h1 h2
      rcases hab with h | h <;> contradiction
    have hi : LinearIndependent (ZMod 2)
        (![basisVector 0,(vec 0 a b 0 0 0 0).val] : Fin 2 → Carrier (ZMod 2)) := by
      rw [linearIndependent_fin2]
      refine ⟨hn,?_⟩
      intro t ht
      have h := congrFun ht 0
      simp [vec,basisVector] at h
    have hr : Set.range (![basisVector 0,(vec 0 a b 0 0 0 0).val] :
        Fin 2 → Carrier (ZMod 2)) = {basisVector 0,(vec 0 a b 0 0 0 0).val} := by
      ext x; simp [or_comm]
    have hh := finrank_span_eq_card hi
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
      (Set.range (![basisVector 0,(vec 0 a b 0 0 0 0).val] : Fin 2 → Carrier (ZMod 2)))) = 2 at hh
    rw [hr] at hh
    exact hh
  · intro x hx y hy
    obtain ⟨r,s,rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨t,u,rfl⟩ := Submodule.mem_span_pair.mp hy
    ext i
    fin_cases i <;> simp [vec,basisVector,Atlas.SplitOctonion.mul]
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide,mul_zero]
private def rootLine (a b : ZMod 2) (hab : a ≠ 0 ∨ b ≠ 0) : ZeroProductLine (ZMod 2) :=
  ⟨rootPlane a b,rootPlane_line a b hab⟩
private theorem rootLine_incident (a b : ZMod 2) (hab : a ≠ 0 ∨ b ≠ 0) :
    pointOnLine firstPoint (rootLine a b hab) := by
  rw [firstPoint_on_line_iff]
  exact Submodule.subset_span (by simp)
private theorem rootLine_mem (a b : ZMod 2) (hab : a ≠ 0 ∨ b ≠ 0) (x : T) :
    x ∈ weylMap.line (rootLine a b hab) ↔
      ∃ r s : ZMod 2, r • vec 1 0 0 0 0 0 0 + s • vec 0 a b 0 0 0 0 = x := by
  rw [SingularMap.line,weyl_image]
  change x.val ∈ rootPlane a b ↔ _
  rw [rootPlane,Submodule.mem_span_pair]
  have he : (vec 1 0 0 0 0 0 0).val = basisVector 0 := by
    ext i; fin_cases i <;> simp [vec,basisVector]
  constructor
  · rintro ⟨r,s,hh⟩
    refine ⟨r,s,Subtype.ext ?_⟩
    simpa only [Submodule.coe_add,Submodule.coe_smul,he] using hh
  · rintro ⟨r,s,hh⟩
    refine ⟨r,s,?_⟩
    simpa only [Submodule.coe_add,Submodule.coe_smul,he] using congrArg Subtype.val hh
private theorem root_moved (a b : ZMod 2) (hab : a ≠ 0 ∨ b ≠ 0) :
    subspaceCommutator σ ⊤ (Subgroup.zpowers (rootActor a b 0)) =
      weylMap.line (rootLine a b hab) := by
  apply le_antisymm
  · apply cyclic_le
    intro x
    rw [rootLine_mem,root_diff]
    refine ⟨a*x.val 6+b*x.val 5,x.val 7,?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [vec,mul_comm]
  · let M := subspaceCommutator σ ⊤ (Subgroup.zpowers (rootActor a b 0))
    have hd (x : T) : σ (rootActor a b 0) x-x ∈ M :=
      Submodule.subset_span ⟨_,Subgroup.mem_zpowers _,x,Submodule.mem_top,rfl⟩
    have hdir : vec 0 a b 0 0 0 0 ∈ M := by
      simpa [root_diff,vec] using hd (vec 0 0 0 0 0 0 1)
    have h0 : vec 1 0 0 0 0 0 0 ∈ M := by
      rcases hab with ha | hb
      · simpa [root_diff,vec,ha] using hd (vec 0 0 0 0 0 a⁻¹ 0)
      · simpa [root_diff,vec,hb] using hd (vec 0 0 0 0 b⁻¹ 0 0)
    intro x hx
    obtain ⟨r,s,rfl⟩ := (rootLine_mem a b hab x).mp hx
    exact M.add_mem (M.smul_mem r h0) (M.smul_mem s hdir)
private def spaceEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) V) (g : Model (ZMod 2)) :
    V ≃ₗ[ZMod 2] V where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv := ρ.inv_self_apply g
  right_inv := ρ.self_inv_apply g
private theorem span_conj {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) V)
    (A : Subgroup (Model (ZMod 2))) (g : Model (ZMod 2)) :
    (fixedSpaceSpan ρ A).map (ρ g) = fixedSpaceSpan ρ (A.map (MulAut.conj g).toMonoidHom) := by
  apply fixedSpaceSpan_map_equivariant ρ ρ _ (MulAut.conj g).injective (spaceEquiv ρ g)
  intro a x
  change ρ g (ρ a x) = ρ (g*a*g⁻¹) (ρ g x)
  simp only [map_mul,Module.End.mul_apply,ρ.inv_self_apply]
private theorem perp_conj {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : SingularMap V) (ρ : Representation (ZMod 2) (Model (ZMod 2)) V)
    (hf : f.Equivariant ρ) (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    (perpendicular f p).map (ρ g) = perpendicular f (g • p) := by
  ext w
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨σ g x,?_,(hf g x).symm⟩
    change normPolar (g • p).val.rep (g.val x.val) = 0
    rw [smul_rep,automorphism_normPolar]
    exact hx
  · rintro ⟨x,hx,rfl⟩
    change normPolar (g • p).val.rep x.val = 0 at hx
    have he : g.val ((σ g⁻¹ x).val) = x.val :=
      congrArg Subtype.val ((traceZeroAction (ZMod 2)).self_inv_apply g x)
    refine ⟨f.linear (σ g⁻¹ x),⟨σ g⁻¹ x,?_,rfl⟩,?_⟩
    · change normPolar p.val.rep ((σ g⁻¹ x).val) = 0
      rw [← automorphism_normPolar g,he]
      simpa only [smul_rep] using hx
    · rw [hf,(traceZeroAction (ZMod 2)).self_inv_apply]
/-- In the Weyl module each nonidentity member of the derived pencil centralizer
moves precisely one of the actual zero-product lines through the marked point. -/
theorem weyl_nonidentity_moved (p : SingularPoints (ZMod 2)) (b : Model (ZMod 2))
    (hb : b ∈ derivedCentralizer weylMap σ p) (hne : b ≠ 1) :
    ∃ L : ZeroProductLine (ZMod 2), pointOnLine p L ∧
      subspaceCommutator σ ⊤ (Subgroup.zpowers b) = weylMap.line L := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg,inv_smul_smul]
  have hc : derivedCentralizer weylMap σ p =
      BinaryCore.natural.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← derivedCentralizer_firstPoint weylMap σ weylMap_equivariant,
      derivedCentralizer_conjugate weylMap σ weylMap_equivariant,hp]
  rw [hc] at hb
  obtain ⟨b,hb,rfl⟩ := hb
  have hbne : b ≠ 1 := by intro h; simp [h] at hne
  obtain ⟨a,c,rfl⟩ := (natural_roots b).mp hb
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra! h
    exact hbne (by rw [h.1,h.2,root_zero])
  refine ⟨g⁻¹ • rootLine a c hac,?_,?_⟩
  · rw [← hp]
    exact (pointOnLine_smul_iff _ _ _).mpr (rootLine_incident a c hac)
  · rw [weylMap.line_equivariant σ weylMap_equivariant,
      ← root_moved a c hac,subspaceCommutator_top_map_conj,MonoidHom.map_zpowers]
/-- The element fixed spaces of the Weyl pencil four span exactly the polar
hyperplane in Aschbacher–Smith 14.7.55(4). -/
theorem weyl_fixedSpaceSpan (p : SingularPoints (ZMod 2)) :
    fixedSpaceSpan σ (derivedCentralizer weylMap σ p) = perpendicular weylMap p := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg,inv_smul_smul]
  rw [← hp,← derivedCentralizer_conjugate weylMap σ weylMap_equivariant,
    ← span_conj,derivedCentralizer_firstPoint weylMap σ weylMap_equivariant,
    base_fixedSpan,← base_perp,perp_conj weylMap σ weylMap_equivariant]
/-- The Weyl polar perpendicular has codimension one. -/
theorem weyl_perpendicular_codim (p : SingularPoints (ZMod 2)) :
    Module.finrank (ZMod 2) (T ⧸ perpendicular weylMap p) = 1 := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have he : (perpendicular weylMap p).map (spaceEquiv σ g).toLinearMap =
      perpendicular weylMap firstPoint := by
    change (perpendicular weylMap p).map (σ g) = _
    rw [perp_conj weylMap σ weylMap_equivariant,hg]
  rw [(Submodule.Quotient.equiv _ _ (spaceEquiv σ g) he).finrank_eq,base_perp]
  exact base_codim
/-- All four spaces in the full-actor clause agree, including the full-group
fixed summand of the Weyl module. -/
theorem weyl_full_spaces (p : SingularPoints (ZMod 2)) (a : Model (ZMod 2))
    (ha : a ∈ fullCentralizer weylMap σ p)
    (hout : a ∉ derivedCentralizer weylMap σ p) :
    pencilSpan weylMap p ⊔ fixedSpace σ ⊤ = fixedSpace σ (Subgroup.zpowers a) ∧
    fixedSpace σ (Subgroup.zpowers a) = fixedSpace σ (derivedCentralizer weylMap σ p) ∧
    fixedSpace σ (derivedCentralizer weylMap σ p) =
      subspaceCommutator σ ⊤ (fullCentralizer weylMap σ p) := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg,inv_smul_smul]
  have hA : fullCentralizer weylMap σ p =
      BinaryCore.elementary.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← fullCentralizer_firstPoint weylMap σ weylMap_equivariant,
      fullCentralizer_conjugate weylMap σ weylMap_equivariant,hp]
  have hB : derivedCentralizer weylMap σ p =
      BinaryCore.natural.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← derivedCentralizer_firstPoint weylMap σ weylMap_equivariant,
      derivedCentralizer_conjugate weylMap σ weylMap_equivariant,hp]
  rw [hA] at ha
  obtain ⟨a,ha,rfl⟩ := ha
  obtain ⟨u,v,c,rfl⟩ := (elementary_roots a).mp ha
  have hc : c = 1 := by
    have hb : ∀ c : ZMod 2, c=0 ∨ c=1 := by decide
    rcases hb c with rfl | h
    · exact False.elim (hout (hB ▸ ⟨rootActor u v 0,(natural_roots _).mpr ⟨u,v,rfl⟩,rfl⟩))
    · exact h
  subst c
  have hP : pencilSpan weylMap p ⊔ fixedSpace σ ⊤ = baseFixed.map (σ g⁻¹) := by
    rw [← base_pencil_fixed,Submodule.map_sup,pencilSpan_equivariant weylMap σ
      weylMap_equivariant,hp,fixedSpace_map_conj]
    simp
  rw [hP,hA,hB,← MonoidHom.map_zpowers,← fixedSpace_map_conj,
    ← fixedSpace_map_conj,← subspaceCommutator_top_map_conj,outer_fixed,base_fixed,base_moved]
  exact ⟨rfl,rfl,rfl⟩
private theorem norm_scalar_add {F : Type*} [Field F] (r : F) (x : Carrier F) :
    Atlas.SplitOctonion.norm (r • unit + x) =
      r^2 + r * trace x + Atlas.SplitOctonion.norm x := by
  simp only [Atlas.SplitOctonion.norm,unit,Pi.add_apply,Pi.smul_apply,smul_eq_mul,trace]
  simp
  ring
private theorem quotient_fix (g : Model (ZMod 2)) (x : T) :
    action (ZMod 2) g (mk (ZMod 2) x) = mk (ZMod 2) x ↔ σ g x = x := by
  rw [action_mk]
  constructor
  · intro h
    obtain ⟨r,hr⟩ := (mk_eq_mk_iff (ZMod 2) _ _).mp h
    have he : (σ g x).val = r • unit + x.val := eq_add_of_sub_eq hr.symm
    have hn : Atlas.SplitOctonion.norm (σ g x).val = Atlas.SplitOctonion.norm x.val :=
      automorphism_norm g x.val
    rw [he,norm_scalar_add,show trace x.val=0 from x.property,mul_zero,add_zero] at hn
    have hr2 : r^2 = 0 := add_right_cancel (show r^2 + Atlas.SplitOctonion.norm x.val =
      0 + Atlas.SplitOctonion.norm x.val by simpa only [zero_add] using hn)
    have hr0 : r=0 := eq_zero_of_pow_eq_zero hr2
    apply Subtype.ext
    simpa only [hr0,zero_smul,zero_add] using he
  · exact congrArg (mk (ZMod 2))
private theorem quotient_fixed (A : Subgroup (Model (ZMod 2))) :
    (fixedSpace σ A).map (mk (ZMod 2)) = fixedSpace (action (ZMod 2)) A := by
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩ g
    exact (quotient_fix g.val x).mpr (hx g)
  · intro hv
    obtain ⟨x,rfl⟩ := mk_surjective (ZMod 2) v
    exact ⟨x,fun g => (quotient_fix g.val x).mp (hv g),rfl⟩
private theorem quotient_fixedSpan (A : Subgroup (Model (ZMod 2))) :
    (fixedSpaceSpan σ A).map (mk (ZMod 2)) = fixedSpaceSpan (action (ZMod 2)) A := by
  simp only [fixedSpaceSpan,Submodule.map_iSup,quotient_fixed]
private theorem quotient_moved (A : Subgroup (Model (ZMod 2))) :
    (subspaceCommutator σ ⊤ A).map (mk (ZMod 2)) =
      subspaceCommutator (action (ZMod 2)) ⊤ A := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,x,_,rfl⟩
    change mk (ZMod 2) (σ a x-x) ∈ subspaceCommutator (action (ZMod 2)) ⊤ A
    rw [map_sub,← action_mk]
    exact Submodule.subset_span ⟨a,ha,mk (ZMod 2) x,Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,x,_,rfl⟩
    obtain ⟨y,rfl⟩ := mk_surjective (ZMod 2) x
    refine ⟨σ a y-y,Submodule.subset_span ⟨a,ha,y,Submodule.mem_top,rfl⟩,?_⟩
    rw [map_sub,action_mk]
private theorem quotient_image (P : Submodule (ZMod 2) (Carrier (ZMod 2))) :
    (weylMap.image P).map (mk (ZMod 2)) = naturalMap.image P := by
  rw [weyl_image]
  rfl
private theorem quotient_line (L : ZeroProductLine (ZMod 2)) :
    (weylMap.line L).map (mk (ZMod 2)) = naturalMap.line L := quotient_image L.val
private theorem quotient_pencil (p : SingularPoints (ZMod 2)) :
    (pencilSpan weylMap p).map (mk (ZMod 2)) = pencilSpan naturalMap p := by
  simp only [pencilSpan,Submodule.map_iSup,quotient_line]
private theorem quotient_perp (p : SingularPoints (ZMod 2)) :
    (perpendicular weylMap p).map (mk (ZMod 2)) = perpendicular naturalMap p :=
  quotient_image _
private theorem model_full (p : SingularPoints (ZMod 2)) :
    fullCentralizer naturalMap (action (ZMod 2)) p = fullCentralizer weylMap σ p := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg,inv_smul_smul]
  rw [← hp,← fullCentralizer_conjugate naturalMap (action (ZMod 2)) naturalMap_equivariant,
    ← fullCentralizer_conjugate weylMap σ weylMap_equivariant,
    fullCentralizer_firstPoint naturalMap (action (ZMod 2)) naturalMap_equivariant,
    fullCentralizer_firstPoint weylMap σ weylMap_equivariant]
private theorem model_derived (p : SingularPoints (ZMod 2)) :
    derivedCentralizer naturalMap (action (ZMod 2)) p = derivedCentralizer weylMap σ p := by
  rw [derivedCentralizer,derivedCentralizer,model_full]
/-- The actual scalar quotient carries the Weyl moved line to the natural
moved line, with the same marked incidence. -/
theorem natural_nonidentity_moved (p : SingularPoints (ZMod 2)) (b : Model (ZMod 2))
    (hb : b ∈ derivedCentralizer naturalMap (action (ZMod 2)) p) (hne : b ≠ 1) :
    ∃ L : ZeroProductLine (ZMod 2), pointOnLine p L ∧
      subspaceCommutator (action (ZMod 2)) ⊤ (Subgroup.zpowers b) = naturalMap.line L := by
  rw [model_derived] at hb
  obtain ⟨L,hL,he⟩ := weyl_nonidentity_moved p b hb hne
  refine ⟨L,hL,?_⟩
  rw [← quotient_moved,he,quotient_line]
/-- The sum of the natural element fixed spaces is precisely the actual
image of the marked polar hyperplane. -/
theorem natural_fixedSpaceSpan (p : SingularPoints (ZMod 2)) :
    fixedSpaceSpan (action (ZMod 2)) (derivedCentralizer naturalMap (action (ZMod 2)) p) =
      perpendicular naturalMap p := by
  rw [model_derived,← quotient_fixedSpan,weyl_fixedSpaceSpan,quotient_perp]
private theorem natural_base_codim :
    Module.finrank (ZMod 2) (Space (ZMod 2) ⧸ perpendicular naturalMap firstPoint) = 1 := by
  have hk : scalarLine (ZMod 2) ≤ lastCoord.ker := by
    rw [scalarLine,Submodule.span_singleton_le_iff_mem]
    rfl
  let q := (scalarLine (ZMod 2)).liftQ lastCoord hk
  have hker : q.ker = perpendicular naturalMap firstPoint := by
    rw [← quotient_perp,base_perp]
    ext v
    obtain ⟨x,rfl⟩ := mk_surjective (ZMod 2) v
    constructor
    · intro hx
      exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      rw [← he]
      exact hy
  have hs : Function.Surjective q := fun a => ⟨mk (ZMod 2) (vec 0 0 0 0 0 0 a),rfl⟩
  rw [← hker,(q.quotKerEquivOfSurjective hs).finrank_eq]
  simp
/-- The perpendicular is a hyperplane also in the six-dimensional scalar quotient. -/
theorem natural_perpendicular_codim (p : SingularPoints (ZMod 2)) :
    Module.finrank (ZMod 2) (Space (ZMod 2) ⧸ perpendicular naturalMap p) = 1 := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have he : (perpendicular naturalMap p).map (spaceEquiv (action (ZMod 2)) g).toLinearMap =
      perpendicular naturalMap firstPoint := by
    change (perpendicular naturalMap p).map (action (ZMod 2) g) = _
    rw [perp_conj naturalMap (action (ZMod 2)) naturalMap_equivariant,hg]
  rw [(Submodule.Quotient.equiv _ _ (spaceEquiv (action (ZMod 2)) g) he).finrank_eq]
  exact natural_base_codim
/-- The four full-actor spaces agree in the actual natural quotient. -/
theorem natural_full_spaces (p : SingularPoints (ZMod 2)) (a : Model (ZMod 2))
    (ha : a ∈ fullCentralizer naturalMap (action (ZMod 2)) p)
    (hout : a ∉ derivedCentralizer naturalMap (action (ZMod 2)) p) :
    pencilSpan naturalMap p ⊔ fixedSpace (action (ZMod 2)) ⊤ =
      fixedSpace (action (ZMod 2)) (Subgroup.zpowers a) ∧
    fixedSpace (action (ZMod 2)) (Subgroup.zpowers a) =
      fixedSpace (action (ZMod 2)) (derivedCentralizer naturalMap (action (ZMod 2)) p) ∧
    fixedSpace (action (ZMod 2)) (derivedCentralizer naturalMap (action (ZMod 2)) p) =
      subspaceCommutator (action (ZMod 2)) ⊤ (fullCentralizer naturalMap (action (ZMod 2)) p) := by
  rw [model_full] at ha
  rw [model_derived] at hout
  obtain ⟨h1,h2,h3⟩ := weyl_full_spaces p a ha hout
  have H1 := congrArg (Submodule.map (mk (ZMod 2))) h1
  have H2 := congrArg (Submodule.map (mk (ZMod 2))) h2
  have H3 := congrArg (Submodule.map (mk (ZMod 2))) h3
  rw [Submodule.map_sup,quotient_pencil,quotient_fixed,quotient_fixed] at H1
  rw [quotient_fixed,quotient_fixed,← model_derived] at H2
  rw [quotient_fixed,quotient_moved,← model_derived,← model_full] at H3
  exact ⟨H1,H2,H3⟩
end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors
