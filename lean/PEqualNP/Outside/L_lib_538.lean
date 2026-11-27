import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_538

def sgn (x : ZMod 2) : ℤ := if x = 0 then (1 : ℤ) else -1

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem add_add_self (a b : ZMod 2) : a + b + b = a := by
  fin_cases a <;> fin_cases b <;> rfl

theorem sgn_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgn (∑ i ∈ s, f i) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem single (c p q : ZMod 2) :
    (∑ a : ZMod 2, ∑ b : ZMod 2, sgn (c * (a * b) + p * a + q * b)) =
      if c = 0 then (if p = 0 ∧ q = 0 then 4 else 0) else 2 * sgn (p * q) := by
  have h2 : ∀ f : ZMod 2 → ℤ, ∑ a : ZMod 2, f a = f 0 + f 1 := fun f => Fin.sum_univ_two f
  simp only [h2]
  fin_cases c <;> fin_cases p <;> fin_cases q <;> rfl

theorem expo {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (γ p q u v : Fin s → ZMod 2) :
    (∑ i, γ i * (u i * v i)) +
      (∑ i, p i * (u i + ∑ j ∈ Finset.Iio i, A i j * (u j * v j))) +
      (∑ i, q i * (v i + ∑ j ∈ Finset.Iio i, B i j * (u j * v j))) =
    ∑ j, ((γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)) * (u j * v j)
      + p j * u j + q j * v j) := by
  have hA : (∑ i, ∑ j ∈ Finset.Iio i, p i * (A i j * (u j * v j))) =
      ∑ j, ∑ i ∈ Finset.Ioi j, p i * (A i j * (u j * v j)) := by
    apply Finset.sum_comm'
    intro x y; simp
  have hB : (∑ i, ∑ j ∈ Finset.Iio i, q i * (B i j * (u j * v j))) =
      ∑ j, ∑ i ∈ Finset.Ioi j, q i * (B i j * (u j * v j)) := by
    apply Finset.sum_comm'
    intro x y; simp
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, hA, hB]
  have e1 : ∀ j : Fin s, (∑ i ∈ Finset.Ioi j, p i * A i j * (u j * v j)) =
      ∑ i ∈ Finset.Ioi j, p i * (A i j * (u j * v j)) :=
    fun j => Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∀ j : Fin s, (∑ i ∈ Finset.Ioi j, q i * B i j * (u j * v j)) =
      ∑ i ∈ Finset.Ioi j, q i * (B i j * (u j * v j)) :=
    fun j => Finset.sum_congr rfl (fun i _ => by ring)
  simp only [e1, e2]
  ring

def Phi {s : ℕ} (A B : Fin s → Fin s → ZMod 2)
    (Z : (Fin s → ZMod 2) → (Fin s → ZMod 2) → (Fin s → ZMod 2))
    (xy : (Fin s → ZMod 2) × (Fin s → ZMod 2)) : (Fin s → ZMod 2) × (Fin s → ZMod 2) :=
  (fun i => xy.1 i + ∑ j ∈ Finset.Iio i, A i j * Z xy.1 xy.2 j,
   fun i => xy.2 i + ∑ j ∈ Finset.Iio i, B i j * Z xy.1 xy.2 j)

def Psi {s : ℕ} (A B : Fin s → Fin s → ZMod 2)
    (uv : (Fin s → ZMod 2) × (Fin s → ZMod 2)) : (Fin s → ZMod 2) × (Fin s → ZMod 2) :=
  (fun i => uv.1 i + ∑ j ∈ Finset.Iio i, A i j * (uv.1 j * uv.2 j),
   fun i => uv.2 i + ∑ j ∈ Finset.Iio i, B i j * (uv.1 j * uv.2 j))

theorem psi_phi {s : ℕ} (A B : Fin s → Fin s → ZMod 2)
    (Z : (Fin s → ZMod 2) → (Fin s → ZMod 2) → (Fin s → ZMod 2))
    (hZ : ∀ x y i, Z x y i =
      (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j))
    (xy : (Fin s → ZMod 2) × (Fin s → ZMod 2)) : Psi A B (Phi A B Z xy) = xy := by
  have hz : ∀ j, (Phi A B Z xy).1 j * (Phi A B Z xy).2 j = Z xy.1 xy.2 j :=
    fun j => (hZ xy.1 xy.2 j).symm
  apply Prod.ext <;> funext i
  · show (Phi A B Z xy).1 i +
      ∑ j ∈ Finset.Iio i, A i j * ((Phi A B Z xy).1 j * (Phi A B Z xy).2 j) = xy.1 i
    simp only [hz]
    exact add_add_self _ _
  · show (Phi A B Z xy).2 i +
      ∑ j ∈ Finset.Iio i, B i j * ((Phi A B Z xy).1 j * (Phi A B Z xy).2 j) = xy.2 i
    simp only [hz]
    exact add_add_self _ _

def G {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (γ p q : Fin s → ZMod 2)
    (uv : (Fin s → ZMod 2) × (Fin s → ZMod 2)) : ℤ :=
  sgn ((∑ i, γ i * (uv.1 i * uv.2 i)) + (∑ i, p i * (Psi A B uv).1 i)
    + (∑ i, q i * (Psi A B uv).2 i))

theorem G_eq {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (γ p q u v : Fin s → ZMod 2) :
    G A B γ p q (u, v) = ∏ j, sgn
      ((γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)) * (u j * v j)
        + p j * u j + q j * v j) := by
  rw [← sgn_sum, ← expo]
  rfl

theorem factor {s : ℕ} (t : Fin s → ZMod 2 → ZMod 2 → ℤ) :
    (∑ u : Fin s → ZMod 2, ∑ v : Fin s → ZMod 2, ∏ j, t j (u j) (v j)) =
      ∏ j, ∑ a, ∑ b, t j a b := by
  have h1 : ∀ u : Fin s → ZMod 2, (∑ v : Fin s → ZMod 2, ∏ j, t j (u j) (v j)) =
      ∏ j, ∑ b, t j (u j) b := fun u => (Fintype.prod_sum (fun j b => t j (u j) b)).symm
  simp only [h1]
  exact (Fintype.prod_sum (fun j a => ∑ b, t j a b)).symm

theorem main {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (γ : Fin s → ZMod 2)
    (Z : (Fin s → ZMod 2) → (Fin s → ZMod 2) → (Fin s → ZMod 2))
    (hZ : ∀ x y i, Z x y i =
      (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j))
    (p q : Fin s → ZMod 2) :
    (∑ x : Fin s → ZMod 2, ∑ y : Fin s → ZMod 2,
      sgn ((∑ i, γ i * Z x y i) + (∑ i, p i * x i) + (∑ i, q i * y i))) =
      ∏ j : Fin s,
        if γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j) = 0
        then (if p j = 0 ∧ q j = 0 then 4 else 0)
        else 2 * sgn (p j * q j) := by
  have hs : ∀ x y : Fin s → ZMod 2,
      sgn ((∑ i, γ i * Z x y i) + (∑ i, p i * x i) + (∑ i, q i * y i)) =
        G A B γ p q (Phi A B Z (x, y)) := by
    intro x y
    unfold G
    rw [psi_phi A B Z hZ]
    have : ∀ i, Z x y i = (Phi A B Z (x, y)).1 i * (Phi A B Z (x, y)).2 i := fun i => hZ x y i
    simp only [← this]
  have hinj : Function.Injective (Phi A B Z) :=
    Function.LeftInverse.injective (psi_phi A B Z hZ)
  have hbij : Function.Bijective (Phi A B Z) := Finite.injective_iff_bijective.mp hinj
  simp only [hs]
  rw [← Fintype.sum_prod_type' (fun x y => G A B γ p q (Phi A B Z (x, y)))]
  rw [Function.Bijective.sum_comp hbij (G A B γ p q)]
  rw [Fintype.sum_prod_type]
  simp only [G_eq]
  rw [factor (fun j a b => sgn
      ((γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)) * (a * b) + p j * a + q j * b))]
  exact Finset.prod_congr rfl (fun j _ => single _ _ _)

end PEqualNP.Outside.L_lib_538

theorem PEqualNP.Outside.L_lib_538 : ∀ s : ℕ,
  let V := Fin s → ZMod 2
  let dot := fun (u v : V) => ∑ i : Fin s, u i * v i
  let sign := fun (x : ZMod 2) => if x = 0 then (1 : ℤ) else -1
  ∀ (A B : Fin s → Fin s → ZMod 2) (γ : V) (Z : V → V → V),
  (∀ x y i, Z x y i =
    (x i + ∑ j ∈ Finset.Iio i, A i j * Z x y j) *
    (y i + ∑ j ∈ Finset.Iio i, B i j * Z x y j)) →
  ∀ p q : V,
    let c := fun (j : Fin s) =>
      γ j + ∑ i ∈ Finset.Ioi j, (p i * A i j + q i * B i j)
    (∑ x : V, ∑ y : V, sign (dot γ (Z x y) + dot p x + dot q y)) =
      ∏ j : Fin s,
        if c j = 0 then (if p j = 0 ∧ q j = 0 then 4 else 0)
        else 2 * sign (p j * q j) := by
  intro s V dot sign A B γ Z hZ p q c
  exact PEqualNP.Outside.L_lib_538.main A B γ Z hZ p q
