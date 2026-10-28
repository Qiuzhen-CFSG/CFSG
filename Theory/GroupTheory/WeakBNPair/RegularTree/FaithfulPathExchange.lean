module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCubic
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# Exchange from faithful rank-one coordinates on actual paths

For a half-path root element with upper parameter a, choose the opposite
lower parameter a inverse. Their braid word and the marked reversing
reflection differ by a diagonal element. The full Cartan marking lifts
that difference; injectivity kills its kernel. Thus the braid itself
reverses the path up to its pointwise Cartan, and the opposite root gives
the required exchange actor. Factoring an arbitrary half-path fixer by
the same Cartan proves the literal exchange conclusion.

No natural-module kernel or common-centralizer assumption is needed for
this faithful branch. The source consumer constructs the marked actor,
roots, Cartan and reflection. Source: DGS, Groups and Graphs (1985),
(14.11)--(14.12), pp.217--218.
-/

public noncomputable section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open NaturalCubic SimpleGraph SimpleGraph.Walk
variable {X V F : Type*} [Group X] [MulAction X V] [Field F] [CharP F 2]
variable {Γ : SimpleGraph V} {a b : V}

/-- A faithful actor with opposite root coordinates and its full diagonal
Cartan supplies exchange on the actual half paths. -/
theorem halfFixer_exchange_of_faithful_coordinates
    (p : Γ.Walk a b) (n : ℕ) (hlen : p.length=2*n) (K H : Subgroup X)
    (hK : K ≤ pathFixer (X := X) p)
    (hfactor : (pathFixer (X := X) (p.drop n) : Set X)=
      (pathRoot (X := X) (p.drop n) : Set X)*(K : Set X))
    (hR : pathRoot (X := X) (p.drop n) ≤ H)
    (f : H →* SL(2,F)) (hi : Function.Injective f)
    (hupper : ∀ x : H, (x:X)∈pathRoot (X := X) (p.drop n) → ∃ a : F, f x=upper a)
    (hlower : ∀ y : H, (y:X)∈pathRoot (X := X) (p.take n) → ∃ a : F, f y=lower a)
    (honto : ∀ a : F, ∃ y : H, (y:X)∈pathRoot (X := X) (p.take n) ∧ f y=lower a)
    (hdiag : ∀ a : F, ∀ ha : a≠0, diag2 a ha∈(K.subgroupOf H).map f)
    (u : H) (hu : ∀ k≤2*n, (u:X) • p.getVert k=p.getVert (2*n-k))
    (g : X) (hg : ∀ k, n≤k → k≤2*n → g • p.getVert k=p.getVert k)
    (hmove : g • a≠a) :
    ∃ y : X, (∀ k≤n, y • p.getVert k=p.getVert k) ∧ y • (g • a)=b := by
  have hgF : g∈(pathFixer (X := X) (p.drop n) : Set X) := by
    intro k hk
    rw [drop_length,hlen] at hk
    rw [drop_getVert]
    exact hg (n+k) (by omega) (by omega)
  rw [hfactor] at hgF
  obtain ⟨x,hx,k,hk,rfl⟩ := hgF
  have hka : k • a=a := by simpa only [getVert_zero] using hK hk 0 (Nat.zero_le _)
  have hxa : (x*k) • a=x • a := by rw [mul_smul,hka]
  have hxne : x≠1 := by intro he; rw [hxa,he,one_smul] at hmove; exact hmove rfl
  let xx : H := ⟨x,hR hx⟩
  obtain ⟨c,hc⟩ := hupper xx hx
  have hcne : c≠0 := by
    intro he
    have he' : f xx=f 1 := by rw [hc,he,upper,transvection_coeff_zero,map_one]
    exact hxne (congrArg Subtype.val (hi he'))
  obtain ⟨y,hy,hfy⟩ := honto c⁻¹
  have hxx : x*x=1 := congrArg Subtype.val (hi (by
    rw [map_mul,hc,upper_square,map_one] : f (xx*xx)=f 1))
  have hhalves := pathRoot_halves_reflection p n hlen (u:X) hu
  have hxS : ((u*xx*u⁻¹ : H):X)∈pathRoot (X := X) (p.take n) := by
    rw [←hhalves.2]
    exact ⟨x,hx,rfl⟩
  have hyR : ((u*y*u⁻¹ : H):X)∈pathRoot (X := X) (p.drop n) := by
    rw [←hhalves.1]
    exact ⟨y,hy,rfl⟩
  obtain ⟨d,hd⟩ := hlower (u*xx*u⁻¹) hxS
  obtain ⟨e,he⟩ := hupper (u*y*u⁻¹) hyR
  have hux : f u*upper c=lower d*f u := by
    calc
      _ = f (u*xx*u⁻¹)*f u := by
        simp only [map_mul,map_inv,hc,mul_assoc,inv_mul_cancel,mul_one]
      _ = _ := by rw [hd]
  have huy : f u*lower c⁻¹=upper e*f u := by
    calc
      _ = f (u*y*u⁻¹)*f u := by
        simp only [map_mul,map_inv,hfy,mul_assoc,inv_mul_cancel,mul_one]
      _ = _ := by rw [he]
  obtain ⟨d,hd,hfu⟩ := braid_of_intertwines (f u) c d c⁻¹ e hcne (inv_ne_zero hcne) hux huy
  have hcor := correction_mem f (K.subgroupOf H) c d hcne hd xx y u hc hfy hfu hdiag
  rw [(f.ker_eq_bot_iff).mpr hi,bot_sup_eq] at hcor
  have hcorX : x*(y:X)*x*(u:X)⁻¹∈K := hcor
  have hrev : (x*(y:X)*x) • a=b := by
    have huab : (u:X) • a=b := by
      simpa only [getVert_zero,Nat.sub_zero,←hlen,getVert_length] using hu 0 (Nat.zero_le _)
    calc
      _ = (x*(y:X)*x*(u:X)⁻¹) • ((u:X) • a) := by rw [←mul_smul]; congr 1; group
      _ = (x*(y:X)*x*(u:X)⁻¹) • b := by rw [huab]
      _ = b := by simpa only [getVert_length] using hK hcorX p.length le_rfl
  have hxb : x • b=b := (pathRoot_fixes (p.drop n) hx).1
  have hxxact (v : V) : x • (x • v)=v := by rw [←mul_smul,hxx,one_smul]
  refine ⟨y,?_,?_⟩
  · intro k hk
    have hh := (pCoreIn_le 2 _ hy) k (show k≤(p.take n).length by rw [take_length,hlen]; omega)
    simpa only [take_getVert,min_eq_right hk] using hh
  · rw [hxa]
    simpa only [mul_smul,hxxact,hxb] using congrArg (x • ·) hrev

end Theory.GroupTheory.WeakBNPair.RegularTree
